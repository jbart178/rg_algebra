This directory contains the files for the translation
framework developed as part of the thesis 
"A Translation Framework for Isabelle". 

The files of interest are:

    - RG_Translate.thy
        This is the main entry-point of the translation
        framework and is the theory which is imported by
        other theories if they need to make use of the
        translations provided.
    
    - RG_Relation_Func.thy
        Contains the translation function for the function
        representation of relations.
    
    - RG_Relation_Tuple.thy
        Contains the translation function for the tuple
        representation of relations.

    - utils.ML
        Contains utility methods which are utilised by
        the above theory files. 

    - symbols
        Contains the symbol mapping for the syntax added
        for relations and predicates (i.e. lrel, rrel, 
        lpred and rpred). Also contains mappings for 
        other syntax used in the concurrency theories.

The following files are not part of the framework itself
but were instead used for components of the thesis
and other assessment related to it:

    - Sample_Translation.thy
        Contains the sample translation function which
        is used within the thesis paper itself.

    - Temp_Theory.thy
        A theory which contains different term constructs
        in order to demonstrate the SML structures 
        Isabelle employs. This was used as part of the 
        poster and demonstration assessment.