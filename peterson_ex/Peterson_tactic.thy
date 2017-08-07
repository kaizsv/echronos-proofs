theory Peterson_tactic
  imports 
    Peterson_base
begin
  
ML \<open>
fun timed_tac i ctxt st seq =
  let
    fun str_of_goal th = Pretty.string_of (Goal_Display.pretty_goal ctxt th)

    fun limit f x = Timeout.apply (Time.fromSeconds i) f x
      handle Timeout.TIMEOUT _ =>
        let val _ = warning ("Method timed out:\n"(* ^ (str_of_goal st)*))
        in SOME (st, Seq.empty) end
  in
    Seq.make (limit (fn () => Option.map (apsnd (timed_tac i ctxt st))
      (Seq.pull seq)))
  end
\<close>

ML \<open>
(*Apply second tactic to all subgoals emerging from the first,
  but not the last one --
  following usual convention for subgoal-based tactics.*)
infix 1 THEN_ALL_NEW_BUT_1;

fun (tac1 THEN_ALL_NEW_BUT_1 tac2) i st =
  st |> (tac1 i THEN (fn st' =>
    Seq.INTERVAL tac2 i (i + Thm.nprems_of st' - Thm.nprems_of st - 1) st'));

fun DETERM' tac i = DETERM (tac i)

fun TRY' tac i = TRY (tac i)

fun TRY_EVERY' tacs i = EVERY' (map (fn tac => TRY' tac) tacs) i

fun FORWARD tac ctxt = tac THEN_ALL_NEW_BUT_1 (SOLVED' (assume_tac ctxt))

fun TRY_EVERY_FORWARD' ctxt thms i =
  TRY_EVERY' (map (fn thm => FORWARD (forward_tac ctxt [thm]) ctxt) thms) i
\<close>  
  
  
end
  