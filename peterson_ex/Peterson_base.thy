theory Peterson_base
  imports
    "../verif/OG_More"
    Peterson_state
    "../lib/Hoare_Parallel/OG_Syntax"
    "../lib/subgoal_focus/Subgoal_Methods"
    "../lib/Eisbach_Methods"
begin
  
  
  
  
  
definition
  mutex_init
where
  "mutex_init \<equiv>  
    \<acute>pr1 := 0,,
    \<acute>in1 := False,,
    \<acute>pr2 := 0,,
    \<acute>in2 := False"
  
lemmas Peterson_mutex_base_defs =
  mutex_init_def
  
end
  