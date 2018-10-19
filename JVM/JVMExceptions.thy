(*  Title:      HOL/MicroJava/JVM/JVMExceptions.thy
    Author:     Gerwin Klein, Martin Strecker
    Copyright   2001 Technische Universitaet Muenchen
*)
(*
  Expanded by Susannah Mansky
  2016-17, UIUC
*)

section {* Exception handling in the JVM *}

theory JVMExceptions imports "../Common/Exceptions" JVMInstructions (* "../Common/ClassesAbove" *)
begin

definition matches_ex_entry :: "'m prog \<Rightarrow> cname \<Rightarrow> pc \<Rightarrow> ex_entry \<Rightarrow> bool"
where
  "matches_ex_entry P C pc xcp \<equiv>
                 let (s, e, C', h, d) = xcp in
                 s \<le> pc \<and> pc < e \<and> P \<turnstile> C \<preceq>\<^sup>* C'"


primrec match_ex_table :: "'m prog \<Rightarrow> cname \<Rightarrow> pc \<Rightarrow> ex_table \<Rightarrow> (pc \<times> nat) option"
where
  "match_ex_table P C pc []     = None"
| "match_ex_table P C pc (e#es) = (if matches_ex_entry P C pc e
                                   then Some (snd(snd(snd e)))
                                   else match_ex_table P C pc es)"

abbreviation
  ex_table_of :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> ex_table" where
  "ex_table_of P C M == snd (snd (snd (snd (snd (snd (snd (method P C M)))))))"


fun find_handler :: "jvm_prog \<Rightarrow> addr \<Rightarrow> heap \<Rightarrow> frame list \<Rightarrow> sheap \<Rightarrow> jvm_state"
where
  "find_handler P a h [] sh = (Some a, h, [], sh)"
| "find_handler P a h (fr#frs) sh = 
       (let (stk,loc,C,M,pc,ics) = fr in
         case match_ex_table P (cname_of h a) pc (ex_table_of P C M) of
           None \<Rightarrow> 
              (case M = clinit of
                   True \<Rightarrow> (None, h, ([],loc,C,M,pc,Throwing a)#frs, sh)
                 | _ \<Rightarrow> find_handler P a h frs sh
              )
         | Some pc_d \<Rightarrow> (None, h, (Addr a # drop (size stk - snd pc_d) stk, loc, C, M, fst pc_d, No_ics)#frs, sh))"

lemma find_handler_cases:
 "find_handler P a h frs sh = js
   \<Longrightarrow> (\<exists>frs' sh'. frs' \<noteq> [] \<and> js = (None, h, frs', sh')) \<or> (\<exists>x sh'. js = (Some x, h, [], sh'))"
apply (cut_tac P = "\<lambda>P a h frs sh. \<forall>js. find_handler P a h frs sh = js \<longrightarrow>
  (\<exists>frs' sh'. frs' \<noteq> [] \<and> js = (None, h, frs', sh')) \<or> (\<exists>x sh'. js = (Some x, h, [], sh'))"
  and ?a0.0 = P and ?a1.0 = a and ?a2.0 = h and ?a3.0 = frs and ?a4.0 = sh
 in find_handler.induct, simp) apply (rename_tac P2 a2 h2 fr2 frs2 sh2)
 apply clarsimp apply (rename_tac stk2 loc2 C2 M2 pc2 ics2 frs2 sh2)
 apply (case_tac "M2 = clinit", simp+)
done

lemma find_handler_None:
 "find_handler P a h frs sh = (None, h, frs', sh') \<Longrightarrow> frs' \<noteq> []"
 by (drule find_handler_cases, clarsimp)

lemma find_handler_Some:
 "find_handler P a h frs sh = (Some x, h, frs', sh') \<Longrightarrow> frs' = []"
 by (drule find_handler_cases, clarsimp)

lemma find_handler_Some_same_error_same_heap[simp]:
 "find_handler P a h frs sh = (Some x, h', frs', sh') \<Longrightarrow> x = a \<and> h = h'"
apply (cut_tac P = "\<lambda>P a h frs sh. find_handler P a h frs sh = (Some x, h', frs', sh') \<longrightarrow>
   x = a \<and> h = h'"
  and ?a0.0 = P and ?a1.0 = a and ?a2.0 = h and ?a3.0 = frs and ?a4.0 = sh
 in find_handler.induct, simp) apply (rename_tac P2 a2 h2 fr2 frs2 sh2)
 apply clarsimp apply (rename_tac stk2 loc2 C2 M2 pc2 ics2 frs2 sh2)
 apply (case_tac "M2 = clinit", simp+)
done


lemma find_handler_prealloc_pres:
assumes "preallocated h"
shows "find_handler P a h frs sh = (xp',h',frs',sh')
  \<Longrightarrow> preallocated h'"
using assms
proof(induct frs)
  case (Cons f frs) then show ?case using assms by(cases f, cases "curr_method f = clinit", auto)
qed(simp)

end
