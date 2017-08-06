theory Example_proof
imports
    Example_tactic
begin
  
definition same_target
  where
    "same_target \<equiv> (\<acute>x:=0)"
    
lemmas same_target_defs =
  same_target_def
  
end
  