theory Peterson_proof_final
  imports
    "../verif/OG_Composition"
begin
  
lemma oghoare_assumed_inv_cong:
  "J = J' \<Longrightarrow> oghoare_inv J Inv p c q = oghoare_inv J' Inv p c q"
  by simp

lemma oghoare_assumed_inv_cong':
  "oghoare_inv J Inv p c q \<Longrightarrow> J = J' \<Longrightarrow> oghoare_inv J' Inv p c q"
  by simp

lemma oghoare_inv_cong:
  "Inv = Inv' \<Longrightarrow> oghoare_inv J Inv p c q = oghoare_inv J Inv' p c q"
  by simp

lemma oghoare_inv_cong':
  "oghoare_inv J Inv p c q \<Longrightarrow> Inv = Inv' \<Longrightarrow> oghoare_inv J Inv' p c q"
  by simp

theorem oghoare_inv_strengthen_assm:
  "oghoare_inv J  In p  c  q  \<Longrightarrow>  
   oghoare_inv (J\<inter>J') In p c q"
  unfolding oghoare_inv_def
  by (erule oghoare_strengthen_assm)
    
(* insert *)
    
    
lemma [simp]:
  "\<lbrace>True\<rbrace> = UNIV"
  by simp

lemma will_not_fail_merge_same_prog_com: 
  "same_prog_com cs cs' \<Longrightarrow> merge_prog_com cs cs' = Some (the (merge_prog_com cs cs'))"
  apply (subst option.collapse)
   apply (rule ccontr)
   apply (clarsimp simp: no_merge_imp_not_same_prog_com)
  apply simp
  done
  
  
  
end
  