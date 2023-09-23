theory RG_Translate
  imports 
    "RG_Relation_Tuple"
begin

section \<open>About the RG Translate library\<close>

text \<open>
The Rely-Guarantee Translation framework is an easily
extendible set of syntax translations for the 
Rely-Guarantee calculus.

This file is the main entry point for this framework.
Any theories which require the syntax translations it
provides need to import this theory directly. 

DO NOT import the sub-theories directly as they are
subject to naming or structural changes which can 
break theories which make direct reference to them.
\<close>

end