package de.tu_dresden.lat.scripts

import java.io.{File, FileOutputStream}

import scala.jdk.CollectionConverters._
import org.semanticweb.owlapi.apibinding.OWLManager
import org.semanticweb.owlapi.model._
import org.semanticweb.owlapi.model.parameters.Imports
import uk.ac.manchester.cs.owlapi.modularity.{ModuleType, SyntacticLocalityModuleExtractor}

/**
 * Analyse different DLs occurring in genuine modules. Here, we focus on EL, FL0, their intersection, and the rest of
 * OWL.
 */
object DLsInModules {

  def main(args: Array[String]) = {
    val manager = OWLManager.createOWLOntologyManager()
    val ontology = manager.loadOntologyFromOntologyDocument(new File(args(0)))

    ontology.removeAxioms(ontology.aboxAxioms(Imports.INCLUDED)) // we do not care about abox axioms yet

    {
      val partitioning = collectAxioms(ontology)

      println("Axioms Counts - " +
        "FL0: " + partitioning.fl0Module.size +
        " EL: " + partitioning.elModule.size +
        " both: " + partitioning.bothModule.size +
        " rest: " + partitioning.rest.size)
    }

    {
      val partitioning = collectModules(ontology)

      println("Module Sizes - " +
        "FL0: " + partitioning.fl0Module.size +
        " EL: " + partitioning.elModule.size +
        " both: " + partitioning.bothModule.size +
        " rest: " + partitioning.rest.size)

      val fl0fragment = manager.createOntology(partitioning.fl0Module.asJavaCollection)
      fl0fragment.addAxioms(partitioning.bothModule.asJava)
      manager.saveOntology(fl0fragment, new FileOutputStream(new File(args(0)+".fl0")))
    }
  }

  case class Partitioning(fl0Module: Set[OWLAxiom],
                          elModule: Set[OWLAxiom],
                          bothModule: Set[OWLAxiom],
                          rest: Set[OWLAxiom])

  def collectAxioms(ontology: OWLOntology): Partitioning = {
    var rest = Set[OWLAxiom]()
    var elModule = Set[OWLAxiom]()
    var fl0Module = Set[OWLAxiom]()
    var bothModule = Set[OWLAxiom]()

    ontology.tboxAxioms(Imports.INCLUDED).forEach(ax => getDL(ax) match {
      case DescriptionLogic.BOTH =>
        //elModule += ax
        //fl0Module += ax
        bothModule += ax
      case DescriptionLogic.EL =>
        elModule += ax
      case DescriptionLogic.FL0 =>
        fl0Module += ax
      case DescriptionLogic.NONE =>
        rest += ax
    }
    )

    Partitioning(fl0Module, elModule, bothModule, rest)
  }

  def collectModules(ontology: OWLOntology) = {

    val moduleExtractor = new SyntacticLocalityModuleExtractor(
      ontology.getOWLOntologyManager,
      ontology,
      ModuleType.STAR)


    var toProcess = ontology.logicalAxioms(Imports.INCLUDED).iterator().asScala.toSet[OWLAxiom]

    var rest = Set[OWLAxiom]()
    var elModule = Set[OWLAxiom]()
    var fl0Module = Set[OWLAxiom]()
    var bothModule = Set[OWLAxiom]()

    while(!toProcess.isEmpty) {
      var nextAxiom = toProcess.head

      toProcess -= nextAxiom

      var signature = nextAxiom.getSignature

      var module = moduleExtractor
        .extract(signature)
        .asScala
        .filter(_.isLogicalAxiom)



      getDL(module) match {

        case DescriptionLogic.BOTH =>
          bothModule ++= module
          //elModule ++= module
          //fl0Module ++= module
          toProcess --= module

        case  DescriptionLogic.EL =>
          elModule ++= module

        case DescriptionLogic.FL0 =>
          fl0Module ++= module

        case DescriptionLogic.NONE =>
          rest += nextAxiom
      }
    }

    Partitioning(fl0Module, elModule, bothModule, rest)
  }


  object DescriptionLogic extends Enumeration {
    type DescriptionLogic = Value
    val EL, FL0, BOTH, NONE = Value
  }
  import DescriptionLogic._

  def getDL(axioms: Iterable[OWLAxiom]): DescriptionLogic = {
    val dls =  axioms.map(getDL)
    if(dls.forall(_==DescriptionLogic.BOTH))
      DescriptionLogic.BOTH
    else if(dls.forall(Set(DescriptionLogic.BOTH, DescriptionLogic.EL)))
      DescriptionLogic.EL
    else if(dls.forall(Set(DescriptionLogic.BOTH,DescriptionLogic.FL0)))
      DescriptionLogic.FL0
    else {
   /*   println("None: ")
      axioms.foreach(ax => println(" "+getDL(ax)+": "+ax))
      println()
    */  DescriptionLogic.NONE
    }
  }

  def getDL(axiom: OWLAxiom) : DescriptionLogic = {
    if(inELandFL0(axiom)) {
      DescriptionLogic.BOTH
    } else if(inEL(axiom))
      DescriptionLogic.EL
    else if(inFL0(axiom))
      DescriptionLogic.FL0
    else
      DescriptionLogic.NONE
  }

  def inELandFL0(axiom: OWLAxiom) = {
    (axiom.isInstanceOf[OWLSubClassOfAxiom] ||
      axiom.isInstanceOf[OWLEquivalentClassesAxiom] ||
      axiom.isInstanceOf[OWLDisjointClassesAxiom]) && (
      axiom.nestedClassExpressions()
        .allMatch(cl => cl.isOWLThing || cl.isOWLNothing ||
          cl.isInstanceOf[OWLClass] ||
            cl.isInstanceOf[OWLObjectIntersectionOf])
        )
  }


  def inEL(axiom: OWLAxiom) = {
    (axiom.isInstanceOf[OWLSubClassOfAxiom] ||
      axiom.isInstanceOf[OWLEquivalentClassesAxiom] ||
      axiom.isInstanceOf[OWLDisjointClassesAxiom]) ||
      axiom.isInstanceOf[OWLObjectPropertyDomainAxiom] && (
      axiom.nestedClassExpressions()
        .allMatch(cl =>  cl.isOWLThing || cl.isOWLNothing ||
          cl.isInstanceOf[OWLClass] ||
            cl.isInstanceOf[OWLObjectIntersectionOf] ||
            cl.isInstanceOf[OWLObjectSomeValuesFrom])
        )
  }


  def inFL0(axiom: OWLAxiom) = {
    (axiom.isInstanceOf[OWLSubClassOfAxiom] ||
      axiom.isInstanceOf[OWLEquivalentClassesAxiom] ||
      axiom.isInstanceOf[OWLDisjointClassesAxiom]) ||
      axiom.isInstanceOf[OWLObjectPropertyRangeAxiom] && (
      axiom.nestedClassExpressions()
        .allMatch(cl => cl.isOWLThing || cl.isOWLNothing ||
          cl.isInstanceOf[OWLClass] ||
            cl.isInstanceOf[OWLObjectIntersectionOf] ||
            cl.isInstanceOf[OWLObjectAllValuesFrom])
        )
  }
}
