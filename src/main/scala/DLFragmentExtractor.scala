import java.io.{File, FileOutputStream}

import datatypes.enumerations.DL
import datatypes.enumerations.DL.DL
import de.tu_dresden.lat.scripts.DLsInModules.{collectAxioms, collectModules}
import org.semanticweb.owlapi.apibinding.OWLManager
import org.semanticweb.owlapi.model._
import org.semanticweb.owlapi.model.parameters.Imports

import scala.jdk.CollectionConverters._

object DLFragmentExtractor {

  def main(args: Array[String]) = {

    val inputFile = new File(args(0))

    val targetDir = args(1);

    val outputFile = new File(targetDir+"/"+inputFile.getName)

    if(outputFile.exists()){
      println("Output file exists: "+outputFile)
      System.exit(1)
    }

    val manager = OWLManager.createOWLOntologyManager()
    val ontology = manager.loadOntologyFromOntologyDocument(inputFile)

    ontology.removeAxioms(ontology.aboxAxioms(Imports.INCLUDED)) // we do not care about abox axioms yet


      val partitioning = collectAxioms(ontology)

      println("Axioms Counts - " +
        "FL0: " + partitioning.fl0Module.size +
        " EL: " + partitioning.elModule.size +
        " both: " + partitioning.bothModule.size +
        " rest: " + partitioning.rest.size)


      val fl0fragment = manager.createOntology(partitioning.fl0Module.asJavaCollection)
      fl0fragment.addAxioms(partitioning.bothModule.asJava)


      manager.saveOntology(fl0fragment, new FileOutputStream(outputFile))

  }
}
