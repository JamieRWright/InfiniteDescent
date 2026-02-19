# README #

This is the Isabelle mechanization associated to the paper "Certified Infinite Descent Criteria in Isabelle/HOL".

### Overview ###

This folder has 4 top level theories, a session graph and a ROOT file along with 2 subfolders and an auxiliary subfolder for the browsable Isabelle HTML developed during our work. Each file and folder has a brief overview along with the key definitions/results from the paper found in them. The folder is structured as follows:

Session_Graph.pdf -- A visual representation of the theory structure for this work.

ROOT - ROOT file used to build the Isabelle session for this project

Top level theories:

Preliminaries.thy:
    Contains auxillary facts and definitions, including generic LTL lemmas over streams.
    
Buchi_Preliminaries.thy:
    Imports the Buchi_Complementation AFP entry and provides additional introduction and elimination rules, along with supplimentary lemmas regarding language inclusion.

Directed_Graphs.thy:
    This theory mechanizes the (Directed) Graph locale, along with all definitions and results relevant to it's context, as seen in Section 2.2 (defined in Section 2.1).

Sloped_Graphs.thy:
    Mechanization of the Sloped_Graphs locale, containing key lemmas and the Infinite Descent definition, as seen in Section 2.2 (Definitions 1,2,3).


Subfolders and their contents:

docs: 
    A folder containing the browsable HTML version of each Isabelle file contained in this folder

Criterion:
    The development of each criterion outlined in the paper

    -- VLA_Criterion.thy:
        Imports the Buchi_Preliminaries file to mechanize the VLA Criterion, as seen in Section 3.1 (Definition 4 & 5 and Theorem 6).

    -- SLA_Criterion.thy:
        Imports the Buchi_Preliminaries file to mechanize the SLA Criterion, as seen in Section 3.1 (Definition 7 & 8 and Theorem 9). 
        
    -- Relation_Based_Criterion.thy:
        Definitions related to, and completeness proof of the relation based criterion as seen in Section 3.2 (Definition 10 and Theorem 11).

    -- Incomplete_Criteria.thy:
        Definitions and soundness proofs of the (Extended) Sprenger-Dam Criteria as seen in Section 4.1 (Definition 12, 14, 15 & 16 and Prop. 13 & 17).
        
    -- SD_Incomplete.thy:
        A demonstration of incompleteness for the Sprenger-Dam Criterion, as described in Section 4.1.2.

    -- XSD_Incomplete.thy:
        A demonstration of incompleteness for the Extended Sprenger-Dam Criterion, as described in  Section 4.1.1 (Example 18).

    -- Flat_Cycles_Criterion.thy:
        A proof of soundness for the Flat Cycles criterion as seen in Section 4.2 (Theorem 19)

    -- Descending_Unicycles_Criterion.thy:
        A proof of (relative) completeness for the Descending Unicycles criterion as seen in Section 5.1 (Definition 20 & 21 and Theorem 22)

    -- All.thy:
        Imports all of the above criterion to make each available for a given instantiation, this is the main theory to import.




Examples:
    A collection of concrete instantiations of the Sloped Graph locale, and (dis)proofs of Infinite Descent.

    -- Flat_Aux.thy:
        The instantiation of the Flat_Aux call graph as detailed in Section 2.3. (Figure 1)

    -- Flat_Aux_SLA.thy:
        A demonstration of Infinite Descent proved for Flat_Aux sloped graph using the SLA criterion.

    -- Flat_Aux_VLA.thy:
        A demonstration of Infinite Descent proved for Flat_Aux sloped graph using the VLA criterion.

    -- Flat_Cycle_Example.thy:
        A disproof of Infinite Descent using the Flat Cycles Criterion seen in Section 5.1 (Example 24). This example is Fig. 4b from "Cyclone: A Heterogeneous Tool for Verifying Infinite Descent" - Cohen et al.

    -- Descending_Unicycles_Example.thy:
        A proof of Infinite Descent using the Descending Unicycles Criterion described in Section 5.1. Namely Fig. 6a from "Cyclone: A Heterogeneous Tool for Verifying Infinite Descent" - Cohen et al. This theory also verifies that this graph does not satisfy the Flat Cycles criterion.

    -- Descending_Unicycles_CounterExample.thy:
        A disproof of Infinite Descent using the Descending Unicycles Criterion described in Section 5.1. Namely Fig. 6b from "Cyclone: A Heterogeneous Tool for Verifying Infinite Descent" - Cohen et al.
        
### How to run, and browsable version ###

The folder includes the source (theory) files, which can be run with the latest version of Isabelle, namely Isabelle2025, available for download from 
[https://isabelle.in.tum.de/](https://isabelle.in.tum.de/)

The theory scripts can be inspected by opening Isabelle in interactive mode. They can also be processed in batch mode using the command

`isabelle build -D . -v`

where "isabelle" is an alias for 
the full path to the Isabelle2025 executable. (Details on how to download/install Isabelle and locale the Isabelle executable are operating-system specific and can be found on the [installation instructions from the Isabelle website](https://isabelle.in.tum.de/installation.html)).

The archive also contains a browsable (html) version of the theories, located in the subfolder `Browsable`. The entry point for navigation is, as usual, the file index.html. The command we used to produce these is

`isabelle build -D . -o browser_info -v`
