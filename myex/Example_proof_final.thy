theory Example_proof_final
  imports
    Example_proof
    "../verif/OG_Composition"
begin
  
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
    
lemmas same_prog_all_invs =
  same_prog_merge[]
  
end
  
