theory Example_proof
imports
    Example_tactic
begin
  
(**************** base ******************)
lemmas last_tl' = last_tl[symmetric, THEN subst, rotated]
lemmas set_tl = list.set_sel(2)[rotated]
  
lemmas Collect_conj_eq_rev = Collect_conj_eq[symmetric]
(****************************************)
  
definition same_target
  where
    "same_target \<equiv> (\<acute>x:=0)"
    
lemmas same_target_defs =
  same_target_def
  
lemma same_target_prop_proof:
  "\<lbrace>True\<rbrace> \<parallel>-\<^sub>i \<lbrace>True\<rbrace> \<lbrace>True\<rbrace> same_target \<lbrace>True\<rbrace>"
  unfolding same_target_defs
  unfolding (*inv_defs*) oghoare_inv_def
  apply (simp add: add_inv_aux_def o_def
              del: last.simps butlast.simps)
  apply oghoare
  (*apply (find_goal \<open>succeeds \<open>rule subsetI[where A=UNIV]\<close>\<close>)*)
  (*subgoal*)
  apply clarsimp
  done
  
end
  