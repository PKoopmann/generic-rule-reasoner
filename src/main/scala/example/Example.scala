package example

import genericInferencer.{GenericInferencer, InferenceRule, SimpleGCISpecification}
import org.semanticweb.owlapi.apibinding.OWLManager
import org.semanticweb.owlapi.model.{IRI, OWLSubClassOfAxiom}

import scala.jdk.CollectionConverters.SetHasAsScala

object Example {

  val manager = OWLManager.createOWLOntologyManager()
  val factory = manager.getOWLDataFactory()

  def main(args: Array[String]): Unit = {
    // create the inferencer and our rules to it
    val owlSpec = new SimpleGCISpecification()
    val inferencer = new GenericInferencer(owlSpec)
    inferencer.rules++=createRules()

    // axioms from which the entailment should hold
    var axioms = List[OWLSubClassOfAxiom]()
    axioms ::=
      factory.getOWLSubClassOfAxiom(
        factory.getOWLClass("Human"),
        factory.getOWLClass("Mammal")
      )

    axioms ::=
      factory.getOWLSubClassOfAxiom(
        factory.getOWLClass("Mammal"),
        factory.getOWLClass("Animal")
      )

    axioms ::=
      factory.getOWLSubClassOfAxiom(
        factory.getOWLClass("Human"),
        factory.getOWLObjectSomeValuesFrom(
          factory.getOWLObjectProperty("hasParent"),
          factory.getOWLClass("Human")
        )
      )


    // axioms from which the entailment should be derived:

    // the axiom that should be entailed
    val expectedEntailment = factory.getOWLSubClassOfAxiom(
      factory.getOWLClass("Human"),
      factory.getOWLObjectSomeValuesFrom(
        factory.getOWLObjectProperty("hasParent"),
        factory.getOWLClass("Mammal")
      )
    )

    // check whether we can derive this axiom with our rules
    inferencer.checkEntailment(axioms, expectedEntailment, maxSteps = 100, print=true)

  }

  def createRules(): Set[InferenceRule[OWLSubClassOfAxiom]] = {
    var result = Set[InferenceRule[OWLSubClassOfAxiom]]()


    // First rule: A1 SubClassOf A2, A2 SubClassOf A3 ---> A1 SubClassOf A3
    val premises1 = List(
      factory.getOWLSubClassOfAxiom(
        factory.getOWLClass("A1"),
        factory.getOWLClass("A2")
      ),
      factory.getOWLSubClassOfAxiom(
        factory.getOWLClass("A2"),
        factory.getOWLClass("A3")
      )
    )
    val conclusion1 =
      factory.getOWLSubClassOfAxiom(
        factory.getOWLClass("A1"),
        factory.getOWLClass("A3")
      )

    val rule1 = InferenceRule(premises1,conclusion1)

    // Second rule: A1 SubClassOf r some A2, A2 SubClassOf A3 ---> A1 SubClassOf r some A3
    val premises2 = List(
      factory.getOWLSubClassOfAxiom(
        factory.getOWLClass("A1"),
        factory.getOWLObjectSomeValuesFrom(
          factory.getOWLObjectProperty("r"),
          factory.getOWLClass("A2")
        )
      ),
      factory.getOWLSubClassOfAxiom(
        factory.getOWLClass("A2"),
        factory.getOWLClass("A3")
      )
    )
    val conclusion2 =
      factory.getOWLSubClassOfAxiom(
        factory.getOWLClass("A1"),
        factory.getOWLObjectSomeValuesFrom(
          factory.getOWLObjectProperty("r"),
          factory.getOWLClass("A3")
        )
      )

    val rule2 = InferenceRule(premises2,conclusion2)

    // Thirs rule: from nothing, we derive A SubClassOf A
    val premises3 = List[OWLSubClassOfAxiom]()
    val conclusion3 =
      factory.getOWLSubClassOfAxiom(
        factory.getOWLClass("A"),
        factory.getOWLClass("A")
      )

    val rule3 = InferenceRule(premises3,conclusion3)

    // Adding all the rules
    result += rule1
    result += rule2
    //result += rule3

    return result
  }
}
