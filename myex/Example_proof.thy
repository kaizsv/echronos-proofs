theory Example_proof
imports
    Example_tactic
begin
  
(**************** base ******************)
lemmas last_tl' = last_tl[symmetric, THEN subst, rotated]
lemmas set_tl = list.set_sel(2)[rotated]
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

  apply (find_goal \<open>succeeds \<open>rule subsetI[where A=UNIV]\<close>\<close>)
  subgoal
  apply clarsimp
  apply (tactic \<open>fn thm => if Thm.nprems_of thm > 0 then
        let val ctxt = @{context}
            val clarsimp_ctxt = (ctxt
                addsimps @{thms Int_Diff card_insert_if
                                insert_Diff_if Un_Diff}
                delsimps @{thms disj_not1}
                addSIs @{thms last_tl'})

            val clarsimp_ctxt2 = (ctxt
                addsimps @{thms neq_Nil_conv}
                delsimps @{thms disj_not1}
                addDs @{thms })
                           |> Splitter.add_split @{thm if_split_asm}
                           |> Splitter.add_split @{thm if_split}

            val clarsimp_ctxt3 = (put_simpset HOL_basic_ss ctxt)

            val fastforce_ctxt = (ctxt
                addsimps @{thms last_tl}
                addDs @{thms })
                           |> Splitter.add_split @{thm if_split_asm}
                           |> Splitter.add_split @{thm if_split}

                          in
        timeit (fn _ => Cache_Tactics.PARALLEL_GOALS_CACHE 1 ((TRY' o SOLVED' o DETERM') (
        ((set_to_logic ctxt
        THEN_ALL_NEW svc_commute ctxt
        THEN_ALL_NEW (((fn tac => fn i => DETERM (tac i))
                        (TRY_EVERY_FORWARD' ctxt
                                            @{thms set_tl})
                         THEN'
                         ((TRY' o REPEAT_ALL_NEW)
                             (FORWARD (dresolve_tac ctxt
                                  @{thms  })
                                  ctxt)))
                THEN' (TRY' (clarsimp_tac clarsimp_ctxt3))
                THEN' (TRY' (
                        SOLVED' (fn i => fn st => timed_tac 30 clarsimp_ctxt st (clarsimp_tac clarsimp_ctxt i st))
                ORELSE' SOLVED' (fn i => fn st => timed_tac 30 clarsimp_ctxt2 st (clarsimp_tac clarsimp_ctxt2 i st))
                ORELSE' SOLVED' (clarsimp_tac (ctxt delsimps @{thms disj_not1}
                           |> Splitter.add_split @{thm if_split_asm}) THEN_ALL_NEW
                                (fn i => fn st => timed_tac 20 fastforce_ctxt st (fast_force_tac fastforce_ctxt i st)))
                )))
                ))) 1)
                thm |> Seq.pull |> the |> fst |> Seq.single) end
        else Seq.empty\<close>)
  done
  
end
  