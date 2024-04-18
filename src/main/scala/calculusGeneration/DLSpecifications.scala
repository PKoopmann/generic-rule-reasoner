package calculusGeneration

import java.util.stream.Collectors
import org.semanticweb.HermiT.Reasoner
import org.semanticweb.owlapi.apibinding.OWLManager
import org.semanticweb.owlapi.model.{IRI, OWLAxiom, OWLAxiomVisitorEx, OWLClass, OWLClassExpression, OWLClassExpressionVisitorEx, OWLObjectAllValuesFrom, OWLObjectIntersectionOf, OWLObjectSomeValuesFrom, OWLObjectUnionOf, OWLObjectVisitorEx, OWLSubClassOfAxiom}

import scala.jdk.CollectionConverters._
import scala.jdk.javaapi.{CollectionConverters => S2J}

class SimpleGCISpecification extends Specification[OWLSubClassOfAxiom,OWLClassExpression] {
  val classSpecification = new SimpleClassSpecification

  val factory = classSpecification.factory
  val reasoner = classSpecification.reasoner

  override def matchSequence(pattern: OWLSubClassOfAxiom, sentence: OWLSubClassOfAxiom,
                             initialMap: Map[OWLClassExpression, OWLClassExpression])
  : Option[Map[OWLClassExpression, OWLClassExpression]] =
    classSpecification.matchSequence(pattern.getSubClass,sentence.getSubClass, initialMap) match {
      case None => None
      case Some(map1) => classSpecification.matchSequence(pattern.getSuperClass,sentence.getSuperClass,map1) match {
        case None => None
        case Some(map2) => Some(map1++map2)
      }
    }

  override def applySubstitution(sentence: OWLSubClassOfAxiom, map: Map[OWLClassExpression, OWLClassExpression])
  : OWLSubClassOfAxiom = {
    factory.getOWLSubClassOfAxiom(classSpecification.applySubstitution(sentence.getSubClass(),map),
      classSpecification.applySubstitution(sentence.getSuperClass(),map))
  }

  override def minimalSymbols: Seq[OWLSubClassOfAxiom] =
    classSpecification.minimalSymbols.flatMap( c1 =>
      classSpecification.minimalSymbols.map(c2 =>
      factory.getOWLSubClassOfAxiom(c1,c2))
    )

  override def refine(sentence: OWLSubClassOfAxiom): Seq[OWLSubClassOfAxiom] = {
    classSpecification.refine(sentence.getSubClass).map(factory.getOWLSubClassOfAxiom(_,sentence.getSuperClass))++
    classSpecification.refine(sentence.getSuperClass).map(factory.getOWLSubClassOfAxiom(sentence.getSubClass,_))
  }

  override def validInference(premises: Seq[OWLSubClassOfAxiom], conclusion: OWLSubClassOfAxiom): Boolean = {
    reasoner.getRootOntology().addAxioms(premises.asJavaCollection)
    //println("Axioms: "+reasoner.getRootOntology.getAxioms())
    //println("Check for entailment: "+conclusion)
    reasoner.flush()
    val result = if(!reasoner.isConsistent())
      true
    else
      reasoner.isEntailed(conclusion)
    //println("Entailed: "+result)
    reasoner.getRootOntology().removeAxioms(premises.asJavaCollection)
    result
  }

  override def size(sentence: OWLSubClassOfAxiom): Double =
    classSpecification.size(sentence.getSubClass)+classSpecification.size(sentence.getSuperClass)

  override def variables(sentence: OWLSubClassOfAxiom): Set[OWLClass] =
    classSpecification.variables(sentence.getSubClass)++classSpecification.variables(sentence.getSuperClass)

  override def maxVarIndex(sentence: OWLSubClassOfAxiom): Int =
    List(classSpecification.maxVarIndex(sentence.getSubClass),
      classSpecification.maxVarIndex(sentence.getSuperClass)).max

  override def terms(sentence: OWLSubClassOfAxiom): Set[OWLClassExpression] =
    classSpecification.terms(sentence.getSubClass)++classSpecification.terms(sentence.getSuperClass)
}

class SimpleClassSpecification extends Specification[OWLClassExpression,OWLClassExpression] {

  // No support for role variables - we assume there is only one role
  // (without role hierarchies no real need for anything else)

  object DLConstructor extends Enumeration {
    type DLConstructor = Value

    val TOP, BOTTOM, CONJUNCTION, DISJUNCTION, EXISTS, FORALL = Value
  }

  val supported = DLConstructor.ValueSet(
    DLConstructor.CONJUNCTION,
    DLConstructor.EXISTS,
    //DLConstructor.BOTTOM
  )


  val manager = OWLManager.createOWLOntologyManager();
  val factory = manager.getOWLDataFactory();

  val reasoner = new Reasoner.ReasonerFactory().createReasoner(manager.createOntology())

  override def matchSequence(pattern: OWLClassExpression,
                             sentence: OWLClassExpression,
                             initialMap: Map[OWLClassExpression, OWLClassExpression])
  : Option[Map[OWLClassExpression, OWLClassExpression]] = (pattern,sentence) match {
    case (cl:OWLClass, se: OWLClass) if cl.isOWLThing && se.isOWLThing => Some(initialMap)
    case (cl:OWLClass, se: OWLClass) if cl.isOWLNothing && se.isOWLNothing => Some(initialMap)
    case (cl:OWLClass, sentence) if initialMap.contains(cl) => {
      if(initialMap(cl).equals(sentence))
        Some(initialMap)
      else
        None
    }
    case (cl: OWLClass,sentence) if !cl.isTopEntity && !cl.isBottomEntity => Some(initialMap.+((cl,sentence)))
    case (cl: OWLObjectIntersectionOf, se: OWLObjectIntersectionOf) => {
      if(!(cl.getOperandsAsList.size==2) || !(se.getOperandsAsList.size==2))
        throw new IllegalArgumentException("only supports binary conjunction  -  "+cl+", "+se)
      matchSequence(cl.getOperandsAsList.get(0), se.getOperandsAsList.get(0), initialMap) match {
        case None => None
        case Some(newMap) =>
          val map = initialMap ++ newMap
          matchSequence(cl.getOperandsAsList.get(1), se.getOperandsAsList.get(1), map) match {
            case None => None
            case Some(newMap) => Some(newMap ++ map)
          }
        }
      }
    case (cl: OWLObjectUnionOf, se: OWLObjectUnionOf) => {
      if(!(cl.getOperandsAsList.size==2) || !(se.getOperandsAsList.size==2))
        throw new IllegalArgumentException("only supports binary conjunction  -  "+cl+", "+se)
      matchSequence(cl.getOperandsAsList.get(0), se.getOperandsAsList.get(0), initialMap) match {
        case None => None
        case Some(newMap) =>
          val map = initialMap ++ newMap
          matchSequence(cl.getOperandsAsList.get(1), se.getOperandsAsList.get(1), map) match {
            case None => None
            case Some(newMap) => Some(newMap ++ map)
          }
      }
    }
    case (cl: OWLObjectSomeValuesFrom, se: OWLObjectSomeValuesFrom ) if cl.getProperty.equals(se.getProperty) => {
      matchSequence(cl.getFiller, se.getFiller, initialMap)
    }
    case (cl: OWLObjectAllValuesFrom, se: OWLObjectAllValuesFrom ) if cl.getProperty.equals(se.getProperty) => {
      matchSequence(cl.getFiller, se.getFiller, initialMap)
    }
    case _ => None // nothing could be matched
  }

  override def applySubstitution(sentence: OWLClassExpression, map: Map[OWLClassExpression, OWLClassExpression]): OWLClassExpression =
    sentence.accept(new OWLClassExpressionVisitorEx[OWLClassExpression] {
      override def visit(cl: OWLClass) = map.getOrElse(cl,cl)
      override def visit(cl: OWLObjectIntersectionOf) = {
        val conjuncts = cl.getOperandsAsList().asScala.map(_.accept(this))
        assert(conjuncts.size==2)
        conjunction(conjuncts(0), conjuncts(1))
      }
      override def visit(cl: OWLObjectUnionOf) = {
        val disjuncts = cl.getOperandsAsList().asScala.map(_.accept(this))
        assert(disjuncts.size==2)
        disjunction(disjuncts(0), disjuncts(1))
      }
      override def visit(cl: OWLObjectSomeValuesFrom) = {
        factory.getOWLObjectSomeValuesFrom(cl.getProperty, cl.getFiller.accept(this))
      }
      override def visit(cl: OWLObjectAllValuesFrom) = {
        factory.getOWLObjectAllValuesFrom(cl.getProperty, cl.getFiller.accept(this))
      }
    })

  override def minimalSymbols: Seq[OWLClassExpression] = {
    List(factory.getOWLClass(IRI.create("A")))
  }

  private val firstRole = factory.getOWLObjectProperty(IRI.create("R"))

  override def refine(sentence: OWLClassExpression): Seq[OWLClassExpression] =
    minimalSymbols.flatMap(s =>
      if(s.equals(sentence))
        None
      else {
        var result = Set[OWLClassExpression]()
        if(supported.contains(DLConstructor.CONJUNCTION))
          result ++= Set(conjunction(s,sentence))++Set(conjunction(sentence,s))
        if(supported.contains(DLConstructor.DISJUNCTION))
          result ++= Set(disjunction(s,sentence))++Set(conjunction(sentence,s))
        result
      }
    ) ++ {
      var result = Set[OWLClassExpression]()

      if(supported.contains(DLConstructor.EXISTS))
        result ++= Set(factory.getOWLObjectSomeValuesFrom(firstRole, sentence))

      if(supported.contains(DLConstructor.FORALL))
        result ++= Set(factory.getOWLObjectAllValuesFrom(firstRole, sentence))

      result
    } ++
      (sentence match {
    case cl: OWLClass if cl.isTopEntity || cl.isBottomEntity => Seq()
    case cl: OWLClass if !cl.isTopEntity && !cl.isBottomEntity => {
      var result = nextConcept(cl)::Nil
      if(supported.contains(DLConstructor.TOP))
        result = factory.getOWLThing()::result
      if(supported.contains(DLConstructor.BOTTOM))
        result = factory.getOWLNothing()::result
      result
    }
    case int: OWLObjectIntersectionOf => {
      if (int.getOperandsAsList().size() != 2)
        throw new IllegalArgumentException("Only supports binary conjunction")
      else {
        val c1 = int.getOperandsAsList().get(0)
        val c2 = int.getOperandsAsList().get(1)
        refine(c2).filter(!_.equals(c1)).map(conjunction(c1, _)) ++
          refine(c1).filter(!_.equals(c2)).map(conjunction(_, c2))
      }
    }
    case uni: OWLObjectUnionOf => {
      if (uni.getOperandsAsList().size() != 2)
        throw new IllegalArgumentException("Only supports binary conjunction")
      else {
        val c1 = uni.getOperandsAsList().get(0)
        val c2 = uni.getOperandsAsList().get(1)
        refine(c2).filter(!_.equals(c1)).map(conjunction(c1, _)) ++
          refine(c1).filter(!_.equals(c2)).map(conjunction(_, c2))
      }
    }
    case ex: OWLObjectSomeValuesFrom => {
      refine(ex.getFiller).map{
        factory.getOWLObjectSomeValuesFrom(ex.getProperty,_)
      }
    }
    case all: OWLObjectAllValuesFrom => {
      refine(all.getFiller).map{
        factory.getOWLObjectAllValuesFrom(all.getProperty,_)
      }
    }
  })


  private def conjunction(c1: OWLClassExpression, c2: OWLClassExpression): OWLClassExpression = {
    if(c1.equals(c2))
      return c1;
    val result = factory.getOWLObjectIntersectionOf(c1,c2)
    assert(result.getOperandsAsList.size==2)
    result;
  }

  private def disjunction(c1: OWLClassExpression, c2: OWLClassExpression): OWLClassExpression = {
    if(c1.equals(c2))
      return c1;
    val result = factory.getOWLObjectUnionOf(c1,c2)
    assert(result.getOperandsAsList.size==2)
    result;
  }
  override def validInference(premises: Seq[OWLClassExpression], conclusion: OWLClassExpression): Boolean =
    reasoner.isEntailed(factory.getOWLSubClassOfAxiom(
      factory.getOWLObjectIntersectionOf(S2J.asJava(premises)), conclusion))

  override def size(sentence: OWLClassExpression): Double = {
    val result = sentence.accept(new OWLClassExpressionVisitorEx[Double] {
      override def visit(cl: OWLClass) = 1
/*        if (cl.isOWLThing || cl.isOWLNothing)
          1
        else if (cl.equals(factory.getOWLClass(IRI.create("A"))))
          1
        else if (conceptPos.contains(cl))
          conceptPos(cl)+1
        else {
          conceptPos = conceptPos.+((cl, counter))
          posConcept = posConcept.+((counter, cl))
          counter += 1
          counter
        }*/

      override def visit(cl: OWLObjectIntersectionOf) =
        S2J.asScala(cl.getOperandsAsList).map(_.accept(this)).sum//+cl.getOperandsAsList.size-1

      override def visit(cl: OWLObjectUnionOf) =
        S2J.asScala(cl.getOperandsAsList).map(_.accept(this)).sum//+cl.getOperandsAsList.size-1

      override def visit(cl: OWLObjectSomeValuesFrom) =
        1+cl.getFiller().accept(this)
      override def visit(cl: OWLObjectAllValuesFrom) =
        1+cl.getFiller().accept(this)
    })
    //println(sentence+" has size "+result)
    result
  }

  override def variables(sentence: OWLClassExpression): Set[OWLClass] = {
    sentence.getClassesInSignature().asScala.filterNot(_.isOWLNothing).filterNot(_.isOWLThing).toSet
  }

  override def maxVarIndex(sentence: OWLClassExpression) = {
    val vars = variables(sentence)
    if(vars.isEmpty)
      -1
    else
      vars.map(x => conceptPos.getOrElse(x,0)).max
  }

  override def terms(sentence: OWLClassExpression): Set[OWLClassExpression] = {
    sentence.getNestedClassExpressions.asScala.toSet
  }

  var counter = 0
  var conceptPos = Map[OWLClass, Int]();
  var posConcept = Map[Int, OWLClass]();

//  conceptPos.+((factory.getOWLClass(IRI.create("A")),0))
//  posConcept.+((0,factory.getOWLClass(IRI.create("A"))))
// TODO: check why it doesn't work

  def nextConcept(cl: OWLClass): OWLClass = {
    conceptPos.get(cl) match {
      case Some(pos) => posConcept.get(pos+1) match {
        case Some(cl2) => cl2
        case None => {
          val cl2 = factory.getOWLClass(IRI.create("A"+counter))
          conceptPos = conceptPos.+((cl2,pos+1))
          posConcept = posConcept.+((pos+1,cl2))
          counter+=1
          cl2
        }
      }
      case None => {
        conceptPos = conceptPos.+((cl,counter))
        posConcept = posConcept.+((counter,cl))
        counter+=1
        val cl2 = factory.getOWLClass(IRI.create("A"+counter))
        conceptPos = conceptPos.+((cl2,counter))
        posConcept = posConcept.+((counter,cl2))
        counter+=1
        cl2
      }
    }
  }

}
