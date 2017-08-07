theory Example_proof_final
  imports
    Example_proof
    "../verif/OG_Composition"
begin

lemma oghoare_assumed_inv_cong:
  "J = J' \<Longrightarrow> oghoare_inv J Inv p c q = oghoare_inv J' Inv p c q"
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
    
lemma same_target_prop_proof':
  "\<lbrace>True\<rbrace> \<parallel>-\<^sub>i \<lbrace>True\<rbrace> \<lbrace>True\<rbrace> same_target \<lbrace>True\<rbrace>"
  apply (subst oghoare_assumed_inv_cong)
  prefer 2
  (*** origin: erule ***)
  apply (rule same_target_prop_proof[THEN oghoare_inv_strengthen_assm,
          where J' = "\<lbrace>True\<rbrace>"])
  apply (subst Collect_conj_eq_rev)
  apply (rule Collect_cong)
  apply (rule iffI[rotated], simp)
  apply (clarsimp)
  done
  
lemma will_not_fail_merge_same_prog_com: 
  "same_prog_com cs cs' \<Longrightarrow> merge_prog_com cs cs' = Some (the (merge_prog_com cs cs'))"
  apply (subst option.collapse)
   apply (rule ccontr)
   apply (clarsimp simp: no_merge_imp_not_same_prog_com)
  apply simp
  done
    
lemma same_prog_merge''':
  "same_prog_ann_com p1 p2 \<Longrightarrow>
   same_prog_ann_com p2 p3 \<Longrightarrow>
   merge_ann_com p2 p3 = Some p4 \<Longrightarrow>
   same_prog_ann_com p1 p4"
  apply (induct p1 p2 arbitrary: p3 p4
                           rule: same_prog_ann_com.induct; clarsimp)
       apply (erule same_prog_ann_com.elims; fastforce split: option.splits)+
  done
    
lemma same_prog_merge'':
  "\<lbrakk>same_prog_aux (a, b) (aa, ba); same_prog_aux (aa, ba) (ab, bb);
        merge_prog_aux (aa, ba) (ab, bb) = Some (ac, bc)\<rbrakk>
       \<Longrightarrow> same_prog_aux (a, b) (ac, bc)"
  apply (clarsimp simp: same_prog_aux_def merge_prog_aux_def)
  apply (clarsimp split: option.splits)
  apply (drule_tac s="Some _" in sym)
  apply clarsimp
  apply (rule same_prog_merge'''; simp)
  done
    
lemma same_prog_merge':
  "\<lbrakk>same_prog_list_aux Ts Ts'; same_prog_list_aux Ts' Ts'';
        merge_prog_list_aux Ts' Ts'' = Some Ts'''\<rbrakk>
       \<Longrightarrow> same_prog_list_aux Ts Ts'''"
  apply (clarsimp simp: same_prog_list_aux_def merge_prog_list_aux_def)
  apply (induct Ts arbitrary: Ts' Ts'' Ts'''; simp)
  apply (clarsimp simp: zip_Cons1 split: list.splits option.splits)
  apply (rule same_prog_merge''; simp)
  done
    
lemma same_prog_merge:
  "same_prog_com p1 p2 \<Longrightarrow>
   same_prog_com p2 p3 \<Longrightarrow>
   same_prog_com p1 (the (merge_prog_com p2 p3))"
  apply (frule will_not_fail_merge_same_prog_com)
  apply (frule_tac cs=p2 in will_not_fail_merge_same_prog_com)
  apply (induct p1 p2 arbitrary: p3 rule: same_prog_com.induct; simp)
      apply (erule same_prog_com.elims; clarsimp split: option.splits)
      apply (rule same_prog_merge'; simp)
     apply (erule same_prog_com.elims; fastforce split: option.splits)+
  done
    
lemma same_prog_all:
  "same_prog_com same_target same_target"
  unfolding same_target_defs same_target''_def
  by auto
    
schematic_goal all_all[simplified]:
  "\<parallel>-\<^sub>i (\<lbrace>True\<rbrace> \<inter> \<lbrace>True\<rbrace>)
        ?p
        ?c
        ?q"
  apply (rule oghoare_inv_cong')
   apply (rule oghoare_composition_merge
          (*[of "\<lbrace>True\<rbrace>" "\<lbrace>True\<rbrace>" "\<lbrace>True\<rbrace>" _ "\<lbrace>True\<rbrace>"]*))
  apply (rule same_target_prop_proof')
    oops
  
end
  
