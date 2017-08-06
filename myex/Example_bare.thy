theory Example_bare
  imports
    Example_state
    "../verif/OG_Bare"
begin
  
definition 
  target :: "('a state_ext) bare_com"
where
  "target \<equiv> \<acute>x:=0"
  
lemmas target_defs =
  target_def
  
  end