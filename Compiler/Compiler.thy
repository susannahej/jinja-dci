(*  Title:      Jinja/Compiler/Compiler.thy

    Author:     Tobias Nipkow
    Copyright   TUM 2003
    Expanded to include statics, class initialization, and method theory by Susannah Mansky
    2018, UIUC
*)

section {* Combining Stages 1 and 2 *}

theory Compiler
imports Correctness1 Correctness2
begin

definition J2JVM :: "J_prog \<Rightarrow> jvm_prog"
where 
  "J2JVM  \<equiv>  compP\<^sub>2 \<circ> compP\<^sub>1"

theorem comp_correct_NonStatic:
assumes wf: "wf_J_prog P"
and "method": "P \<turnstile> C sees M,NonStatic:Ts\<rightarrow>T = (pns,body) in C"
and eval: "P \<turnstile> \<langle>body,(h,[this#pns [\<mapsto>] vs],sh)\<rangle> \<Rightarrow> \<langle>e',(h',l',sh')\<rangle>"
and sizes: "size vs = size pns + 1"    "size rest = max_vars body"
shows "J2JVM P \<turnstile> (None,h,[([],vs@rest,C,M,0,No_ics)],sh) -jvm\<rightarrow> (exception e',h',[],sh')"
(*<*)
proof -
  let ?P\<^sub>1 = "compP\<^sub>1 P"
  have nclinit: "M \<noteq> clinit" using wf_sees_clinit1[OF wf] visible_method_exists[OF "method"]
    sees_method_idemp[OF "method"] by fastforce
  have wf\<^sub>1: "wf_J\<^sub>1_prog ?P\<^sub>1" by(rule compP\<^sub>1_pres_wf[OF wf])
  have fv: "fv body \<subseteq> set (this#pns)"
    using wf_prog_wwf_prog[OF wf] "method" by(auto dest!:sees_wf_mdecl simp:wf_mdecl_def)
  have init: "[this#pns [\<mapsto>] vs] \<subseteq>\<^sub>m [this#pns [\<mapsto>] vs@rest]"
    using sizes by simp
  have "?P\<^sub>1 \<turnstile> C sees M,NonStatic: Ts\<rightarrow>T = (compE\<^sub>1 (this#pns) body) in C"
    using sees_method_compP[OF "method", of "\<lambda>b (pns,e). compE\<^sub>1 (case b of NonStatic \<Rightarrow> this#pns | Static \<Rightarrow> pns) e"]
    by(simp)
  moreover obtain ls' where
    "?P\<^sub>1 \<turnstile>\<^sub>1 \<langle>compE\<^sub>1 (this#pns) body, (h, vs@rest, sh)\<rangle> \<Rightarrow> \<langle>fin\<^sub>1 e', (h',ls', sh')\<rangle>"
    using eval\<^sub>1_eval[OF wf_prog_wwf_prog[OF wf] eval fv init] sizes by auto
  ultimately show ?thesis using comp\<^sub>2_correct[OF wf\<^sub>1] eval_final[OF eval] nclinit
    by(fastforce simp add:J2JVM_def final_def)
qed
(*>*)

theorem comp_correct_Static:
assumes wf: "wf_J_prog P"
and "method": "P \<turnstile> C sees M,Static:Ts\<rightarrow>T = (pns,body) in C"
and eval: "P \<turnstile> \<langle>body,(h,[pns [\<mapsto>] vs],sh)\<rangle> \<Rightarrow> \<langle>e',(h',l',sh')\<rangle>"
and sizes: "size vs = size pns"    "size rest = max_vars body"
and nclinit: "M \<noteq> clinit"
shows "J2JVM P \<turnstile> (None,h,[([],vs@rest,C,M,0,No_ics)],sh) -jvm\<rightarrow> (exception e',h',[],sh')"
(*<*)
proof -
  let ?P\<^sub>1 = "compP\<^sub>1 P"
  have wf\<^sub>1: "wf_J\<^sub>1_prog ?P\<^sub>1" by(rule compP\<^sub>1_pres_wf[OF wf])
  have fv: "fv body \<subseteq> set pns"
    using wf_prog_wwf_prog[OF wf] "method" by(auto dest!:sees_wf_mdecl simp:wf_mdecl_def)
  have init: "[pns [\<mapsto>] vs] \<subseteq>\<^sub>m [pns [\<mapsto>] vs@rest]"
    using sizes by simp
  have "?P\<^sub>1 \<turnstile> C sees M,Static: Ts\<rightarrow>T = (compE\<^sub>1 pns body) in C"
    using sees_method_compP[OF "method", of "\<lambda>b (pns,e). compE\<^sub>1 (case b of NonStatic \<Rightarrow> this#pns | Static \<Rightarrow> pns) e"]
    by(simp)
  moreover obtain ls' where
    "?P\<^sub>1 \<turnstile>\<^sub>1 \<langle>compE\<^sub>1 pns body, (h, vs@rest, sh)\<rangle> \<Rightarrow> \<langle>fin\<^sub>1 e', (h',ls', sh')\<rangle>"
    using eval\<^sub>1_eval[OF wf_prog_wwf_prog[OF wf] eval fv init] sizes by auto
  ultimately show ?thesis using comp\<^sub>2_correct[OF wf\<^sub>1] eval_final[OF eval] nclinit
    by(fastforce simp add:J2JVM_def final_def)
qed
(*>*)

(*************)

(* note: doesn't give the method in question; only useful for existence *)
lemma J2JVM_sees_method:
assumes comp: "J2JVM P\<^sub>0 = P" and method: "P\<^sub>0 \<turnstile> C sees M, b :  Ts\<rightarrow>T = m\<^sub>0 in D"
shows "\<exists>m. P \<turnstile> C sees M, b :  Ts\<rightarrow>T = m in D"
proof -
  obtain P\<^sub>1 where comp\<^sub>1: "P = compP\<^sub>2 P\<^sub>1" and comp\<^sub>0: "P\<^sub>1 = compP\<^sub>1 P\<^sub>0"
    using comp by (simp add: J2JVM_def)
  obtain m\<^sub>1 where method1: "P\<^sub>1 \<turnstile> C sees M, b :  Ts\<rightarrow>T = m\<^sub>1 in D"
    using sees_method_compP[OF method] comp\<^sub>0 by fastforce
  then obtain m where "P \<turnstile> C sees M, b :  Ts\<rightarrow>T = m in D"
    using sees_method_compP[OF method1] comp\<^sub>1 by fastforce
  then show ?thesis by fast
qed

lemma J2JVM_sees_method2:
assumes comp: "J2JVM P\<^sub>0 = P" and method: "P \<turnstile> C sees M, b :  Ts\<rightarrow>T = m in D"
shows "\<exists>m\<^sub>0. P\<^sub>0 \<turnstile> C sees M, b :  Ts\<rightarrow>T = m\<^sub>0 in D"
proof -
  obtain P\<^sub>1 where comp\<^sub>1: "P = compP\<^sub>2 P\<^sub>1" and comp\<^sub>0: "P\<^sub>1 = compP\<^sub>1 P\<^sub>0"
    using comp by (simp add: J2JVM_def)
  obtain m\<^sub>1 where "P\<^sub>1 \<turnstile> C sees M, b :  Ts\<rightarrow>T = m\<^sub>1 in D"
    using comp\<^sub>1 method by(auto dest: sees_method_compPD)
  then obtain m\<^sub>0 where "P\<^sub>0 \<turnstile> C sees M, b :  Ts\<rightarrow>T = m\<^sub>0 in D"
    using comp\<^sub>0 by(auto dest: sees_method_compPD)
  then show ?thesis by fast
qed

lemma
assumes wf: "wf_J_prog P\<^sub>0" and comp[simp]: "J2JVM P\<^sub>0 = P"
shows J2JVM_wf: "wf_prog (\<lambda>P C m. True) P"
proof -
  obtain P\<^sub>1 where P\<^sub>1: "P\<^sub>1 = compP\<^sub>1 P\<^sub>0" "P = compP\<^sub>2 P\<^sub>1" using comp by(simp add: J2JVM_def)
  then have wf\<^sub>1: "wf_J\<^sub>1_prog P\<^sub>1" using compP\<^sub>1_pres_wf[OF wf] by simp
  show ?thesis using wf_prog_compPI[OF _ wf\<^sub>1, where f=compMb\<^sub>2] P\<^sub>1(2) by(auto simp add: wf_mdecl_def)
qed


(**************************************)

lemma assumes comp[simp]: "J2JVM P\<^sub>0 = P" and "P \<turnstile> C sees M,b:Ts \<rightarrow> T = m in D"
shows J2JVM_method_instrs:
 "\<exists>e\<^sub>1. instrs_of P C M = compE\<^sub>2 e\<^sub>1 @ [Return] \<and> ex_table_of P C M = compxE\<^sub>2 e\<^sub>1 0 0"
using assms sees_method_compPD by(fastforce simp: J2JVM_def)

lemma assumes comp[simp]: "J2JVM P\<^sub>0 = P" and sees: "P \<turnstile> C sees M,b:Ts \<rightarrow> T = m in D"
 and wf: "wf_J_prog P\<^sub>0"
shows wf_J2JVM_method_instrs: "\<exists>e\<^sub>1. \<not>sub_RI e\<^sub>1 \<and> instrs_of P C M = compE\<^sub>2 e\<^sub>1 @ [Return]
                                    \<and> ex_table_of P C M = compxE\<^sub>2 e\<^sub>1 0 0"
proof -
  obtain P\<^sub>1 where P\<^sub>1: "P\<^sub>1 = compP\<^sub>1 P\<^sub>0" "P = compP\<^sub>2 P\<^sub>1" using comp by(simp add: J2JVM_def)
  then obtain m' where m': "P\<^sub>1 \<turnstile> C sees M, b :  Ts\<rightarrow>T = m' in D \<and> compMb\<^sub>2 b m' = m"
    using sees_method_compPD sees by fastforce
  then have "\<not>sub_RI m'" using P\<^sub>1(1) sees_wf\<^sub>1_nsub_RI[OF compP\<^sub>1_pres_wf[OF wf]] by clarsimp
  then show ?thesis using m' sees by auto
qed

lemma assumes comp[simp]: "J2JVM P\<^sub>0 = P" and "P \<turnstile> C sees M,b:Ts \<rightarrow> T = m in D"
shows J2JVM_method_instrs_nmt: "instrs_of P C M \<noteq> []"
using J2JVM_method_instrs[OF assms] by clarsimp

(* HERE: currently unused *) (*
 lemma
assumes comp[simp]: "J2JVM P\<^sub>0 = P" and "P \<turnstile> C sees M,b:Ts \<rightarrow> T = m in D" and "wf_J_prog P\<^sub>0"
shows J2JVM_method_instr_len_gt1: "1 < length (instrs_of P C M)"
using wf_J2JVM_method_instrs[OF assms] compE\<^sub>2_nsub_RI_nmt (* <- use TypeComp.compE\<^sub>2_not_Nil *) by clarsimp *)

lemma assumes comp: "J2JVM P\<^sub>0 = P" and "P \<turnstile> C sees M,b:Ts \<rightarrow> T = m in D"
  and "n < length (instrs_of P C M)" and "instrs_of P C M ! n \<noteq> Return"
shows J2JVM_method_instrs_nRet_Suc: "Suc n < length (instrs_of P C M)"
using J2JVM_method_instrs[OF assms(1,2)] assms(3,4) by(auto simp: nth_append split: if_split_asm)

(*
(* HERE: MOVE? *) --- used, but need to decide where to put this relative to TypeComp, for compE\<^sub>2_not_Nil
lemma assumes "P \<turnstile> C sees M,b:Ts \<rightarrow> T = m in D" and comp: "J2JVM P\<^sub>0 = P" and "wf_J_prog P\<^sub>0"
shows J2JVM_method_instrs_nReturn0: "instrs_of P C M ! 0 \<noteq> Return"
using wf_J2JVM_method_instrs[OF assms(2,1,3)] compE\<^sub>2_nsub_RI_nmt compE\<^sub>2_nRet
  by (metis length_greater_0_conv nth_append nth_mem)
*)

(* HERE: MOVE *)
(*** error handling lemmas ***)

lemma
assumes "match_ex_table P C' pc (ex_table_of P C M) = \<lfloor>(t,d)\<rfloor>"
shows ex_table_of_matched: "\<exists>pc1 pc2 C'. (pc1,pc2,C',t,d) \<in> set (ex_table_of P C M)"
proof -
  have "match_ex_table P C' pc (ex_table_of P C M) = \<lfloor>(t,d)\<rfloor>
    \<longrightarrow> (\<exists>pc1 pc2 C'. (pc1,pc2,C',t,d) \<in> set (ex_table_of P C M))"
  proof(induct rule: list.induct[where P="\<lambda>ls. match_ex_table P C' pc ls = \<lfloor>(t,d)\<rfloor>
                           \<longrightarrow> (\<exists>pc1 pc2 C'. (pc1,pc2,C',t,d) \<in> set ls)", of "ex_table_of P C M"])
    case Nil then show ?case by simp
  next
    case (Cons a x)
    then show ?case by(auto simp: matches_ex_entry_def) fastforce
  qed
  then show ?thesis using assms by simp
qed

definition exs :: "ex_table \<Rightarrow> nat set"
where
  "exs xt  \<equiv>  \<Union>(f,t,C,h,d) \<in> set xt. {h}"

lemma exs_subset:
shows "(\<And>pc d. exs(compxE\<^sub>2 e pc d) \<subseteq> {pc..<pc+size(compE\<^sub>2 e)})"
and "(\<And>pc d. exs(compxEs\<^sub>2 es pc d) \<subseteq> {pc..<pc+size(compEs\<^sub>2 es)})"
(*<*)
apply(induct e and es rule: compxE\<^sub>2.induct compxEs\<^sub>2.induct)
apply(fastforce simp: exs_def)+
done
(*>*)

lemma compxE\<^sub>2_exs: "(f,t,C,h,d) \<in> set(compxE\<^sub>2 e 0 0) \<Longrightarrow> h < length (compE\<^sub>2 e)"
using exs_subset(1) by(simp add: exs_def, fastforce)

lemma ex_table_pc:
assumes comp[simp]: "J2JVM P\<^sub>0 = P" and sees: "P \<turnstile> C sees M,b: Ts \<rightarrow> T = m in D"
  and ext: "e \<in> set (ex_table_of P C M)"
shows "fst(snd(snd(snd(e)))) < length (instrs_of P C M)
    \<and> instrs_of P C M ! fst(snd(snd(snd(e)))) \<noteq> Return"
proof -
  let ?d = "fst(snd(snd(snd(e))))"
  obtain body where body: "instrs_of P C M = compE\<^sub>2 body @ [Return]"
    "ex_table_of P C M = compxE\<^sub>2 body 0 0" using J2JVM_method_instrs[OF comp sees] by clarify
  then have "?d < length (compE\<^sub>2 body)" using compxE\<^sub>2_exs[where e=body] ext by(cases e, simp)
  then show ?thesis using compE\<^sub>2_nRet[where e\<^sub>1=body] body by(auto simp: nth_append)
qed

lemma match_ex_table_pc:
assumes comp[simp]: "J2JVM P\<^sub>0 = P" and "P \<turnstile> C sees M,b: Ts \<rightarrow> T = m in D"
 and met: "match_ex_table P C' pc (ex_table_of P C M) = \<lfloor>(h,d)\<rfloor>"
shows "h < length (instrs_of P C M)"
proof -
  obtain pc1 pc2 C' where e: "(pc1,pc2,C',h,d) \<in> set (ex_table_of P C M)"
    using ex_table_of_matched[OF met] by clarsimp
  then show ?thesis using ex_table_pc[OF assms(1,2) e] by simp
qed

lemma match_ex_table_nRet:
assumes comp[simp]: "J2JVM P\<^sub>0 = P" and "P \<turnstile> C sees M,b: Ts \<rightarrow> T = m in D"
 and met: "match_ex_table P C' pc (ex_table_of P C M) = \<lfloor>(h,d)\<rfloor>"
shows "instrs_of P C M ! h \<noteq> Return"
proof -
  obtain pc1 pc2 C' where e: "(pc1,pc2,C',h,d) \<in> set (ex_table_of P C M)"
    using ex_table_of_matched[OF met] by clarsimp
  then show ?thesis using ex_table_pc[OF assms(1,2) e] by simp
qed

end
