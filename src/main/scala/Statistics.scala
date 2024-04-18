import java.io.File

import org.semanticweb.owlapi.model.{OWLObjectAllValuesFrom, OWLOntologyManager}
import org.semanticweb.owlapi.apibinding.OWLManager
import org.semanticweb.owlapi.model.parameters.Imports
object Statistics {

  def main(args: Array[String]) = {
    if(args.size==0) {
      println("ONTOLOGY AXIOMS CONCEPT_NAMES ROLE_NAMES VALUE_RESTRICTIONS")
      System.exit(0);
    }

    val file = new File(args(0));

    val ontology = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(file);

    print(file.getName()+ " ")

    val classCount = ontology.classesInSignature(Imports.INCLUDED)
      .filter(s => !(s.isOWLThing || s.isOWLNothing)).count();

    if(classCount<500) {
      println("Ignored (<500 class names)")
      System.exit(0);
    }

    print(ontology.tboxAxioms(Imports.INCLUDED).count()+" ")
    print(classCount+" ")
    print(ontology.objectPropertiesInSignature(Imports.INCLUDED).count()+" ");
    print(ontology.nestedClassExpressions()
      .filter(_.isInstanceOf[OWLObjectAllValuesFrom]).count);
    println();
  }
}
