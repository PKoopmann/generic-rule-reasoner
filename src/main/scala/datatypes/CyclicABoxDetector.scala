package datatypes

import org.semanticweb.owlapi.apibinding.OWLManager
import org.semanticweb.owlapi.model.{AxiomType, OWLIndividual}

import java.io.File
import scala.collection.mutable

object CyclicABoxDetector {

  def main(args: Array[String]): Unit = {
    val filename = args(0)
    val file = new File(filename)

    print("Loading file...")
    val manager = OWLManager.createOWLOntologyManager()
    val ontology = manager.loadOntologyFromOntologyDocument(file)
    println()

    var reachableFrom = new mutable.HashMap[OWLIndividual,mutable.Set[OWLIndividual]]() with mutable.MultiMap[OWLIndividual,OWLIndividual]
    var reachableTo = new mutable.HashMap[OWLIndividual, mutable.Set[OWLIndividual]]() with mutable.MultiMap[OWLIndividual,OWLIndividual]

    print("Looking for cyles...")
    ontology.axioms(AxiomType.OBJECT_PROPERTY_ASSERTION).forEach(axiom => {
      reachableFrom.addBinding(axiom.getSubject, axiom.getObject)
      reachableFrom(axiom.getSubject).addAll(reachableFrom(axiom.getObject))
      if(reachableFrom(axiom.getSubject).contains(axiom.getSubject)){
        println("Cyclic element: "+axiom.getSubject)
        System.exit(0)
      }
    })

    println("No cycle detected!")
  }
}
