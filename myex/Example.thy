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
  \<acute>x:=\<acute>x+1
  \<parallel>
  \<acute>x:=\<acute>x+2
  COEND)"
  
lemma p:
  "\<parallel>-\<^sub>b \<lbrace>True\<rbrace> \<lbrace>True\<rbrace> 
  gg
  \<lbrace>True\<rbrace>"
  apply (rule oghoare_bareI)
    oops
  
end