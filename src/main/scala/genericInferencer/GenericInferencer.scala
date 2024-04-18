package genericInferencer

import org.semanticweb.HermiT.Reasoner
import org.semanticweb.owlapi.apibinding.OWLManager
import org.semanticweb.owlapi.model.{IRI, OWLDataFactory}

import scala.collection.mutable.ListBuffer

trait Specification[SENTENCE, TERM] {
  def matchSequence(pattern: SENTENCE, sentence: SENTENCE, initialMap: Map[TERM,TERM] = Map[TERM,TERM]()): Option[Map[TERM,TERM]]
  def applySubstitution(sentence: SENTENCE, map: Map[TERM,TERM]): SENTENCE
  def size(sentence: SENTENCE): Double
  def variables(sentence: SENTENCE): Set[_ <: TERM]
  def maxVarIndex(sentence: SENTENCE): Int
  def terms(sentence: SENTENCE): Set[TERM]

}

case class InferenceRule[SENTENCE](premises: Seq[SENTENCE], conclusion: SENTENCE) {
  override def toString =
    premises.mkString("{", ", ", "}")+"  --->  "+conclusion
}

class GenericInferencer[SENTENCE,TERM](specification: Specification[SENTENCE,TERM]) {
  var rules: ListBuffer[InferenceRule[SENTENCE]] = ListBuffer();

  val MAX_SIZE = 10 // maximal size of inferred axioms

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


  /**
   * Returns true if the conclusion can be derived from the premises, or something else speaks against
   * using this combination as a rule.
   */
  def checkEntailment(premises: Seq[SENTENCE], conclusion: SENTENCE, maxSteps: Int, print: Boolean = false): Boolean = {

    val terms = premises.flatMap(specification.terms(_)).toSet++specification.terms(conclusion)

    if(print)
      println("Relevant terms: "+terms)

    if(premises.contains(conclusion))
      return true

    var stepsLeft = maxSteps //premises.size + (maxSteps*rules.size)
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
        if(print)
          println("Trying rule "+rule)
        val tautologies = allInstances(rule.conclusion, specification.variables(rule.conclusion).toSeq, terms)
        if(premises.exists(tautologies)){
          if(print)
            println("One of the premises is a tautology - not a good candidate!")
          return true
        }
        tautologies.foreach(newInference)
        //if(tautologies.exists(newInference))
        //  return true
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

object Test {
  def main(args: Array[String]): Unit ={
    val spec = new SimpleGCISpecification();

    val factory = OWLManager.createOWLOntologyManager().getOWLDataFactory;


    val inferencer =new GenericInferencer(spec)

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

    inferencer.rules+=ruleInQuestion

     inferencer.checkEntailment(premises, conclusion, 500, false )

    //InferenceRule(List(SubClassOf(ObjectIntersectionOf(<A> <A1>) <A2>), SubClassOf(<A1> <A>)),SubClassOf(<A1> ObjectIntersectionOf(<A> <A2>)))
  }
}
