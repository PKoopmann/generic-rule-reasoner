package calculusGeneration

import org.semanticweb.HermiT.Reasoner
import org.semanticweb.owlapi.apibinding.OWLManager
import org.semanticweb.owlapi.model.{IRI, OWLDataFactory}

import scala.collection.mutable.ListBuffer

trait Specification[SENTENCE, TERM] {
  def matchSequence(pattern: SENTENCE, sentence: SENTENCE, initialMap: Map[TERM,TERM] = Map[TERM,TERM]()): Option[Map[TERM,TERM]]
  def applySubstitution(sentence: SENTENCE, map: Map[TERM,TERM]): SENTENCE
  def minimalSymbols: Seq[SENTENCE] // return "minimal" sentences
  def refine(sentence: SENTENCE): Seq[SENTENCE] // return all syntactical refinements of the sentence
                                  // postcondition: all refinements have a larger size (see below)
  def validInference(premises: Seq[SENTENCE], conclusion: SENTENCE ): Boolean
  def size(sentence: SENTENCE): Double
  def variables(sentence: SENTENCE): Set[_ <: TERM]
  def maxVarIndex(sentence: SENTENCE): Int
  def terms(sentence: SENTENCE): Set[TERM]

  def size(rule: InferenceRule[SENTENCE]):Double = {
    size(rule.conclusion)+rule.premises.map(size(_)).sum
  }
}

case class InferenceRule[SENTENCE](premises: Seq[SENTENCE], conclusion: SENTENCE)

class GenericInferencer[SENTENCE,TERM](specification: Specification[SENTENCE,TERM]) {
  var rules: ListBuffer[InferenceRule[SENTENCE]] = ListBuffer();

  def applyRule(rule: InferenceRule[SENTENCE], sentences: Seq[SENTENCE]): Option[SENTENCE] ={

    if(!(rule.premises.size==sentences.size))
      return None;
    else {
      var matching = Map[TERM,TERM]();
      for(i <- 0 to rule.premises.size-1){
        specification.matchSequence(rule.premises(i), sentences(i), matching) match {
          case None => return None;
          case Some(map) => matching++=map;
        }
      }
      //println("- Applying "+rule)
      //println("  on "+sentences)
      //println("Substitution: "+matching)
      return Some(specification.applySubstitution(rule.conclusion,matching))
    }
  }

  def applies(rule: InferenceRule[SENTENCE], premise1: SENTENCE): Boolean ={
    rule.premises.size>0 && specification.matchSequence(rule.premises(0), premise1).isDefined
  }

  def allInstances(pattern: SENTENCE, variables: Seq[TERM], terms: Set[TERM]): Set[SENTENCE] = {
    if(variables.isEmpty){
      Set(pattern)
    } else {
      val nextVar = variables.head
      val nextVars = variables.tail
      var result = Set[SENTENCE]()
      terms.foreach{ term =>
        val nextPattern = specification.applySubstitution(pattern, Map(nextVar -> term))
        if(specification.terms(nextPattern).forall(t => variables.contains(t) || terms(t)))
          result = result.union(allInstances(nextPattern,nextVars,terms))
      }
      result
    }
  }

  val MAX_SIZE = 10

  /**
   * Returns true if the conclusion can be derived from the premises, or something else speaks against
   * using this combination as a rule.
   */
  def checkEntailment(premises: Seq[SENTENCE], conclusion: SENTENCE, maxSteps: Int, print: Boolean = false): Boolean = {

    var terms = premises.flatMap(specification.terms(_)).toSet++specification.terms(conclusion)

    if(premises.contains(conclusion))
      return true

    var stepsLeft = premises.size + (maxSteps*rules.size)
    var toProcess:Seq[SENTENCE] = List()++premises
    var derived:Set[SENTENCE] = Set()++premises;
    //println(derived)

    var change=false
    /**
     * returns true if we can return
     */
    def newInference(newInf: SENTENCE): Boolean = {
      stepsLeft -= 1
      if(print)
        println(stepsLeft+". "+newInf)
      if(!derived(newInf) && specification.size(newInf)<MAX_SIZE) {
        //  println(".. infers " + newInf + " (with "+rule+" on "+next+")")
        if (newInf.equals(conclusion))
          return true;
        derived ++= List(newInf)
        change = true
        //println(derived)
        toProcess ++= List(newInf)
      }
      return false
    }

    rules.foreach(rule => {
      if(rule.premises.isEmpty) {
        var tautologies = allInstances(rule.conclusion, specification.variables(rule.conclusion).toSeq, terms)
        if(premises.exists(tautologies)){
          if(print)
            println("One of the premises is a tautology - not a good candidate!")
          return true
        }
        if(tautologies.exists(newInference))
          return true
      }
    })

    if(print)
      println("tautologies done!")

    while(!toProcess.isEmpty && stepsLeft>0){
      if(print)
        println("Still to process: "+toProcess)
      val next = toProcess.head
      if(print)
        println("NEXT: "+next)
      //println(stepsLeft+".. next axiom: "+next)
      toProcess = toProcess.tail
      if(next.equals(conclusion))
        return true
      rules.foreach(rule => {
        if(print)
          println("RULE: "+rule)
       // println(".. check rule " + rule)
        if (applies(rule, next)) {
          if(print)
            println(".. applies")
          if (rule.premises.size == 1) {
            val newInf = applyRule(rule, List(next)).get
            if(newInference(newInf))
              return true
          } else if (rule.premises.size == 2) {
            derived.foreach(premise2 =>
              if(applyRule(rule, List(next, premise2)).exists(newInference))
                return true
            )
          } else {
            throw new IllegalArgumentException("No support for rules with other than 1 or 2 premises")
          }
          //toProcess ++= List(next) // put to end of queue - we might need it for other inferences
        }
      }
      )
      if(toProcess.isEmpty && change) {
        if(print)
          println("NEW ROUND")
        toProcess ++= derived // we might be able to make new inferences
        change=false
      } else if(toProcess.isEmpty){
        if(print)
          println("No change - we stop here")
      }
      toProcess = toProcess.sortBy(specification.size)
    }
    false
  }
}

class CalculusGeneration {
  var rulesTried = Set[InferenceRule[_]]()

  var objectInQuestion: Object = _

  def learnCalculus[S,T](specification: Specification[S,T], maxSentenceSize: Int, maxSteps: Int): Seq[InferenceRule[S]] = {
    var rules = ListBuffer[InferenceRule[S]]();

    var sentencePatterns = Set[S]()

    var toProcess = Seq[S]() ++ specification.minimalSymbols

    val reasoner = new GenericInferencer[S,T](specification)
    reasoner.rules=rules

    var patternsTried=0

    var ruleCandidates = Set[InferenceRule[S]]()

    while(!toProcess.isEmpty){
      val nextPattern = toProcess.head
      toProcess = toProcess.tail

      patternsTried+=1

      println("Next Pattern: "+nextPattern)
      println("Size: "+specification.size(nextPattern))

      println("Number of patterns: "+sentencePatterns.size)
      println("Patterns: "+sentencePatterns)

      // tautologies
      var ruleCandidate = new InferenceRule[S](List(),nextPattern)
      ruleCandidates +=ruleCandidate
      if(good(specification, ruleCandidate) && sound(specification, ruleCandidate)){// && !redundant(reasoner, ruleCandidate, maxSteps)){
        println("-> NEW RULE LEARNED: "+rules.size+". "+ruleCandidate)
        rules = rules.appended(ruleCandidate)
        reasoner.rules=rules
        rules = nonRedundantRules(reasoner,specification,maxSteps,specification.size(ruleCandidate))
        reasoner.rules=rules
      }

      println()
      println("Rules learned ("+rules.size+"):")
      rules.foreach(println(_))

      // try new rules
      sentencePatterns.foreach(pattern2 => if(!pattern2.equals(nextPattern)){
        println("____________________---------->>>>>> "+sentencePatterns.size)
        if(!pattern2.equals(nextPattern)){
          // unary rules
          var ruleCandidate = new InferenceRule[S](List(nextPattern), pattern2)
          ruleCandidates+=ruleCandidate
          //println("Rule Candidate: "+ruleCandidate)
          if(good(specification, ruleCandidate) && valid(specification,ruleCandidate) && sound(specification, ruleCandidate)){// && !redundant(reasoner, ruleCandidate, maxSteps)){
            println("-> NEW RULE LEARNED: "+rules.size+". "+ruleCandidate)
            rules = rules.appended(ruleCandidate)
            reasoner.rules=rules
            rules = nonRedundantRules(reasoner,specification,maxSteps,specification.size(ruleCandidate))
            reasoner.rules=rules
          }

          // unary rule II
          ruleCandidate = new InferenceRule[S](List(pattern2), nextPattern)
          ruleCandidates+=ruleCandidate
          //println("Rule Candidate: "+ruleCandidate)
          if(good(specification, ruleCandidate) && valid(specification,ruleCandidate) && sound(specification, ruleCandidate)){// && !redundant(reasoner, ruleCandidate, maxSteps)){
            println("-> NEW RULE LEARNED: "+ruleCandidate)
            rules = rules.appended(ruleCandidate)
            reasoner.rules=rules
            rules = nonRedundantRules(reasoner,specification,maxSteps,specification.size(ruleCandidate))
            reasoner.rules=rules
          }

          println()
          println("Rules learned ("+rules.size+"):")
          rules.foreach(println(_))

          // binary rules
          sentencePatterns.foreach(pattern3 => if(!pattern3.equals(nextPattern) && !pattern3.equals(pattern2)){
            var ruleCandidate = new InferenceRule[S](List(nextPattern,pattern3), pattern2)
            ruleCandidates+=ruleCandidate
            //println("Rule Candidate: "+ruleCandidate)

            if(good(specification, ruleCandidate) && valid(specification,ruleCandidate) && sound(specification, ruleCandidate)){// && !redundant(reasoner, ruleCandidate, maxSteps)){
              println("-> NEW RULE LEARNED: "+ruleCandidate)
              rules = rules.appended(ruleCandidate)
              reasoner.rules=rules
              rules = nonRedundantRules(reasoner,specification,maxSteps,specification.size(ruleCandidate))
              reasoner.rules=rules
            }

            ruleCandidate = new InferenceRule[S](List(pattern3,pattern2), nextPattern)
            ruleCandidates+=ruleCandidate
            //println("Rule Candidate: "+ruleCandidate)
            if(good(specification, ruleCandidate) && valid(specification,ruleCandidate) && sound(specification, ruleCandidate)) {// && !redundant(reasoner, ruleCandidate, maxSteps)){
              println("-> NEW RULE LEARNED: "+ruleCandidate)
              rules = rules.appended(ruleCandidate)
              reasoner.rules=rules
              rules = nonRedundantRules(reasoner,specification,maxSteps,specification.size(ruleCandidate))
              reasoner.rules=rules
            }
          })


          println()
          println("Rules learned ("+rules.size+"):")
          rules.foreach(println(_))
        }
      })
      if(nextPattern.equals(objectInQuestion)) {
        println("BOOM!")
        System.exit(1)
      }
      /*if(patternsTried>40) {
        println("Patterns: "+sentencePatterns)
        println("Last pattern: "+nextPattern)
        println("Reached maximum patterns tried!")
        return rules.toList
      }*/

      sentencePatterns = sentencePatterns.+(nextPattern)

      val refinements = specification.refine(nextPattern)
        .filter(specification.maxVarIndex(_)<=2) // maximally 3 variables
        .filter(specification.size(_)<=maxSentenceSize)
        .filter(!sentencePatterns.contains(_))

      println("Refinements of "+nextPattern+": "+refinements)

      // refine the sentences
      toProcess ++= refinements

      toProcess = toProcess.sortBy(specification.size(_)).filter(!_.equals(nextPattern))
    }

    //println("\n All the rules tried: ")
    //ruleCandidates.foreach(println)
    //println("------------")
    rulesTried=ruleCandidates.toSet

    return rules.toList;
  }

  def nonRedundantRules[S,T](reasoner: GenericInferencer[S,T], specification: Specification[S,T], maxSteps: Int, size: Double) = {
    //println("filtering redundant rules")
    var rules = reasoner.rules.clone()
    reasoner.rules.toList.sortBy(-specification.size(_)).filter(specification.size(_)>=size)
      .foreach { rule =>
        //println("\nCheck: " + rule)

        // don't consider larger rules for redundancy test
        //reasoner.rules = rules.filter(specification.size(_)<=specification.size(rule))
        // <--- this optimisation would include undesired rules!
        reasoner.rules = rules
        reasoner.rules -= rule

        if (reasoner.checkEntailment(rule.premises, rule.conclusion, maxSteps,false))
          //println("Redundant rule: " + rule)
          rules -= rule
        else
          rules += rule

      }
    reasoner.rules=rules
    reasoner.rules
  }

  def valid[S,T](specification: Specification[S,T], rule: InferenceRule[S]) = {
    val premiseVars = rule.premises.flatMap(specification.variables(_))
    val result = specification.variables(rule.conclusion).forall(premiseVars.contains(_))
    //println("valid? "+result)
    result
  }

  def good[S](specification: Specification[S,_], rule: InferenceRule[S]) = {
    val all = rule.premises++List(rule.conclusion)
    val result =
      all.map(specification.maxVarIndex).max+1 ==
      all.flatMap(specification.variables).toSet.size

    //println("good? "+result)
    result
  }

  def sound[S](specification: Specification[S,_], rule: InferenceRule[S]) = {
    val result = specification.validInference(rule.premises, rule.conclusion)
    //println("sound? "+result)
    result
  }

  def redundant[S](reasoner: GenericInferencer[S,_], rule: InferenceRule[S], maxSteps: Int) = {
    val result = reasoner.checkEntailment(rule.premises, rule.conclusion, maxSteps)
    //println("redundant? "+result)
    result
  }
}

object Test {
  def main(args: Array[String]): Unit ={
    val spec = new SimpleGCISpecification();
    val cgen = new CalculusGeneration()

    val factory = OWLManager.createOWLOntologyManager().getOWLDataFactory;

    cgen.objectInQuestion =
    factory.getOWLSubClassOfAxiom(
      factory.getOWLObjectSomeValuesFrom(
        factory.getOWLObjectProperty(IRI.create("R")),
        factory.getOWLClass(IRI.create("A2x"))
      ),
      factory.getOWLClass(IRI.create("A1"))
    )

    val rules = cgen.learnCalculus(spec, 3, 400)
    println()
    println("Rules learned ("+rules.size+"):")
    rules.foreach(println(_))

    val inferencer =new GenericInferencer(spec)
    inferencer.rules++==rules

    val premises = List(
      factory.getOWLSubClassOfAxiom(
        factory.getOWLObjectSomeValuesFrom(
          factory.getOWLObjectProperty(IRI.create("R")),
          factory.getOWLClass(IRI.create("A1"))
        ),
        factory.getOWLClass(IRI.create("A2"))
      ),
      factory.getOWLSubClassOfAxiom(
        factory.getOWLClass(IRI.create("A")),
        factory.getOWLClass(IRI.create("A1"))
      )
    )
    val conclusion =
      factory.getOWLSubClassOfAxiom(
        factory.getOWLObjectSomeValuesFrom(
          factory.getOWLObjectProperty(IRI.create("R")),
          factory.getOWLClass(IRI.create("A"))
        ),
        factory.getOWLClass(IRI.create("A2"))
      )

    val ruleInQuestion = InferenceRule(premises,conclusion)
    if(!cgen.rulesTried.contains(ruleInQuestion)){
      println("Never even tried!")
    }
    /*
    factory.getOWLSubClassOfAxiom(
      factory.getOWLObjectIntersectionOf(
        factory.getOWLClass(IRI.create("A")),
        factory.getOWLClass(IRI.create("A1"))
      ),
      factory.getOWLClass(IRI.create("A2"))
    ),
    factory.getOWLSubClassOfAxiom(
      factory.getOWLClass(IRI.create("A1")),
      factory.getOWLClass(IRI.create("A"))
    )*/

/*    val conclusion = factory.getOWLSubClassOfAxiom(
      factory.getOWLClass(IRI.create("A1")),
      factory.getOWLObjectIntersectionOf(
        factory.getOWLClass(IRI.create("A")),
        factory.getOWLClass(IRI.create("A2"))
      ))
*/
     // inferencer.rules-=InferenceRule(premises,conclusion)

     inferencer.checkEntailment(premises, conclusion, 500, false )

    //InferenceRule(List(SubClassOf(ObjectIntersectionOf(<A> <A1>) <A2>), SubClassOf(<A1> <A>)),SubClassOf(<A1> ObjectIntersectionOf(<A> <A2>)))
  }
}
