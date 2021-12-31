# SyDPaCC - SYSTEMATIC DEVELOPMENT OF PROGRAMS FOR PARALLEL AND CLOUD COMPUTING
# Version 0.4

## DEVELOPED BY

- Version 0.4 (December 31, 2021):
  - Frederic Loulergue (Univ. Orléans, INSA Centre Val de Loire, LIFO EA 4022, Orléans, France and Northern Arizona University, Flagstaff, AZ, USA)
  - Jolan Philippe (Northern Arizona University, Flagstaff, AZ, USA)
  
- Versions <= 0.25:
  - Frederic Loulergue (Univ. Orléans, INSA Centre Val de Loire, LIFO EA 4022, Orléans, France)
  - Julien Tesson (LACL, Université Paris Est Créteil, Créteil,  France)
  - Wadoud Bousdira (Univ. Orléans, INSA Centre Val de Loire, LIFO EA 4022, Orléans, France)

## DOCUMENTATION

At the moment, the SyDPaCC documentation is sparse. For an introduction to SyDPaCC, we refer to:

- Frédéric Loulergue, Wadoud Bousdira, and Julien Tesson. [Calculating Parallel Programs in Coq using List Homomorphisms](http://dx.doi.org/10.1007/s10766-016-0415-8). Int J Parallel Prog, 45:300--319, 2017
- Tutorial in French: Frédéric Loulergue, Wadoud Bousdira, and Julien Tesson. Calcul de programmes parallèles avec Coq. In Nicolas Ollinger, editor, Informatique Mathématique une photographie en 2015, collection Alpha, pages 87--134. CNRS Éditions, 2015

## CONTENTS
        
- ``COPYRIGHT``                    Copyright notice
- ``LICENSE``                      License CeCill-C
- ``INSTALL.md``                   Instructions for installation
- ``README.md``                    This file
- ``Support/``	   Supporting libraries
- ``Bsml/``		   Axiomatisation of BSML and verified basic skeletons
- ``Core/``          Library for parallel program calculation
- ``Applications/``  Applications of the framework
- ``Extraction/``    Extraction commands
- ``Uncertified/``   Non extracted-code, thus non verified:
  - the parallel implementation of BSML on top of MPI
  - the main programs calling the extracted applications
- ``Tree/``		   SyDPaCC for trees. This part is experimental, the proofs are not complete yet. 
