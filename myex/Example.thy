theory Example
imports
  "../lib/subgoal_focus/Subgoal_Methods"
  "../lib/Eisbach_Methods"
  "../lib/Rule_By_Method"
  (*OG_Bare*)
  (*OG_Composition*)
  "../verif/OG_Bare"
  "../verif/OG_Composition"
begin
    
record state =
  x :: nat
    
definition gg :: "('a state_ext) bare_com"
  where
  "gg \<equiv> (COBEGIN
  WHILE True DO 
  \<acute>x:=\<acute>x+1
  OD
  \<parallel>
  WHILE True DO
  \<acute>x:=\<acute>x+2
  OD
  COEND)"
  
lemma p:
  "\<parallel>-\<^sub>b  \<lbrace>True\<rbrace> \<lbrace>True\<rbrace> 
  gg
  \<lbrace>False\<rbrace>"
  oops
  
end