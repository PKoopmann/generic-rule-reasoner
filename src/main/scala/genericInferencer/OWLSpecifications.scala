package genericInferencer

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


  private val firstRole = factory.getOWLObjectProperty(IRI.create("R"))


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


}
