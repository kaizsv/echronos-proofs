theory Example_state
  imports
    "../lib/Rule_By_Method"
begin
  
record state =
  x :: nat
  
locale foo
  =
  fixes Red :: "'a state_scheme"
begin
  
lemmas r_surj = state.surjective[of Red,symmetric]
  
lemmas foo = 
  state.update_convs[of "\<lambda>_. X" for X, @ (schematic) \<open>subst (asm) r_surj\<close>,symmetric]
  
lemmas foo' = state.select_convs(1) select_convs
  
lemmas foos = foo'[@ (schematic) \<open>subst (asm) foo(1)\<close>]
  
end
  
lemmas state_upd_simps = foo.foos
  
end
  