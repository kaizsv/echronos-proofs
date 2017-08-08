theory Peterson_state
  imports
    "../lib/Rule_By_Method"
begin
  
record Peterson_state =
  pr1 :: nat
  pr2 :: nat
  in1 :: bool
  in2 :: bool
  hold :: nat
  
locale foo
  =
  fixes Red :: "'a Peterson_state_scheme"
begin
  
lemmas r_surj = Peterson_state.surjective[of Red,symmetric]
  
lemmas foo =
  Peterson_state.update_convs[of "\<lambda>_. X" for X, @ (schematic) \<open>subst (asm) r_surj\<close>,symmetric]
  
lemmas foo' = Peterson_state.select_convs(1) Peterson_state.select_convs(2)
              Peterson_state.select_convs(3) Peterson_state.select_convs(4)
              Peterson_state.select_convs(5) select_convs
              
lemmas foos = foo'[@ (schematic) \<open>subst (asm) foo(1)\<close>]
              foo'[@ (schematic) \<open>subst (asm) foo(2)\<close>]
              foo'[@ (schematic) \<open>subst (asm) foo(3)\<close>]
              foo'[@ (schematic) \<open>subst (asm) foo(4)\<close>]
              foo'[@ (schematic) \<open>subst (asm) foo(5)\<close>]
              foo'[@ (schematic) \<open>subst (asm) foo(6)\<close>]   
  
end
  
lemmas Peterson_state_upd_simps = foo.foos
  
(*-------------------------------------------------------------------------*)

definition
  "mutex_invariante \<equiv> True"
(* Peterson mutex precondition and postcondition *)
definition
  "mutex_precondition state \<equiv> 
    pr1 state = 0 \<and> \<not> in1 state \<and> pr2 state = 0 \<and> \<not> in2 state"
  
definition
  "mutex_postcondition state \<equiv> 
    pr1 state = 0 \<and> \<not> in1 state \<and> pr2 state = 0 \<and> \<not> in2 state"
  
end
  