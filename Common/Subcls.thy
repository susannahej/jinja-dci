(*  Title:      Jinja/Common/Subcls.thy
    Author:    Susannah Mansky, UIUC 2016-17
*)

section {* Theory for the subcls relation *}

theory Subcls
imports TypeRel
begin


(* HERE: should move *)
lemma foldl_if_insert:
 "(f y \<in> foldl (\<lambda>a x. if P (f x) then insert (f x) a else a) s l2)
   = (f y \<in> s \<or> (P (f y) \<and> (\<exists>x. f x = f y \<and> x \<in> set l2)))"
apply (induct l2 arbitrary: s, simp+)
apply force
done

(***************************** Subcls ********************************)

lemma subcls_class_exists: "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* C'; C \<noteq> C' \<rbrakk>
 \<Longrightarrow> \<exists>D' fs ms. class P C = \<lfloor>(D', fs, ms)\<rfloor>"
apply (cut_tac a = C and b = C' and
   P = "\<lambda>C. C \<noteq> C' \<longrightarrow> (\<exists>D' fs ms. class P C = \<lfloor>(D', fs, ms)\<rfloor>)"
  in converse_rtrancl_induct, simp+)
 apply (case_tac "z = C'", clarsimp)
  using subcls1D apply blast
 apply clarsimp
 using subcls1D apply blast
apply simp
done

lemma same_class_same_superclass:
 "\<lbrakk> class P y = class P' y; P \<turnstile> y \<prec>\<^sup>1 z \<rbrakk> \<Longrightarrow> P' \<turnstile> y \<prec>\<^sup>1 z"
apply (drule subcls1D, clarsimp)
apply (rule subcls1I, simp+)
done

(************ Subcls related to methods *************)

lemma sees_methods_subcls_sees_methods:
 "\<lbrakk> P \<turnstile> C sees_methods Mm;
    P \<turnstile> C' \<preceq>\<^sup>* C \<rbrakk>
\<Longrightarrow>
  \<exists>Mm'. P \<turnstile> C' sees_methods Mm'"
using sees_methods_decl_mono by blast

lemma sees_method_sees_methods2:
 "\<lbrakk> P \<turnstile> C sees M,b :  Ts\<rightarrow>T = m in D \<rbrakk> \<Longrightarrow>
  \<exists>Mm'. P \<turnstile> D sees_methods Mm'"
by (meson Method_def sees_methods_idemp)

lemma sees_method_subcls_sees:
 "\<lbrakk> P \<turnstile> C sees M,b :  Ts\<rightarrow>T = m in D;
    P \<turnstile> C' \<preceq>\<^sup>* D \<rbrakk>
\<Longrightarrow> \<exists>Ts T m D b. P \<turnstile> C' sees M,b :  Ts\<rightarrow>T = m in D"
apply (drule sees_method_idemp)
apply (simp add: Method_def, clarify)
apply (frule sees_methods_decl_mono, simp, clarify)
apply (subgoal_tac "\<exists>Ts T m b D. (Mm ++ Mm\<^sub>2) M = \<lfloor>((b, Ts, T, m), D)\<rfloor>")
 prefer 2
 apply (simp add: map_add_Some_iff)
 apply (case_tac "Mm\<^sub>2 M", simp)
 apply (simp, case_tac a, case_tac aa, simp)
apply (erule_tac exE)+ apply (rename_tac Ts' T' m' D' b')
apply (rule_tac x = Ts' in exI, rule_tac x = T' in exI, rule_tac x = m' in exI,
  rule_tac x = b' in exI, rule_tac x = D' in exI, rule_tac x = "Mm ++ Mm\<^sub>2" in exI)
apply simp
done

(* note subcls isn't necessarily a partial order because anti-sym isn't guaranteed
  except when well-formed *)
(* HERE: this isn't used *)
lemma subcls_preorder: "preorder_on UNIV {(C, C'). subcls P C C'}"
apply (clarsimp simp add: preorder_on_def refl_on_def trans_def)
apply (drule widen_subcls)+
apply (simp add: widen_trans)
done

lemma subcls1_single_valued: "single_valued (subcls1 P)"
by (clarsimp simp add: single_valued_def subcls1.simps)

lemma subcls_confluent:
  "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* C'; P \<turnstile> C \<preceq>\<^sup>* C'' \<rbrakk> \<Longrightarrow> P \<turnstile> C' \<preceq>\<^sup>* C'' \<or> P \<turnstile> C'' \<preceq>\<^sup>* C'"
 by (simp add: single_valued_confluent subcls1_single_valued)

(* HERE: for proving the acyclic lemma *)
lemma subcls1_confluent: "\<lbrakk> P \<turnstile> a \<prec>\<^sup>1 b; P \<turnstile> a \<preceq>\<^sup>* c; a \<noteq> c \<rbrakk> \<Longrightarrow> P \<turnstile> b \<preceq>\<^sup>* c"
apply (erule converse_rtranclE, simp)
apply (cut_tac subcls1_single_valued, simp add: single_valued_def, blast)
done

lemma subcls_self_superclass: "\<lbrakk> P \<turnstile> C \<prec>\<^sup>1 C; P \<turnstile> C \<preceq>\<^sup>* D \<rbrakk> \<Longrightarrow> D = C"
apply (erule rtrancl_induct, simp)
apply (simp, cut_tac subcls1_single_valued, simp add: single_valued_def)
apply force
done

lemma subcls_of_Obj_acyclic:
 "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* Object; C \<noteq> D \<rbrakk> \<Longrightarrow> \<not>(P \<turnstile> C \<preceq>\<^sup>* D \<and> P \<turnstile> D \<preceq>\<^sup>* C)"
apply clarify
apply (frule rtrancl_trans [where x = D], simp)
apply (cut_tac b = Object
  and P = "\<lambda>C. \<forall>D. C \<noteq> D \<longrightarrow> \<not>(P \<turnstile> C \<preceq>\<^sup>* D \<and> P \<turnstile> D \<preceq>\<^sup>* C)" in converse_rtrancl_induct, simp)
 apply simp
 apply clarify
 apply (erule_tac x = y in allE)
 apply (case_tac "z = y", simp)
  apply (frule subcls_self_superclass, simp)
  apply (erule subcls1.cases, simp)
 apply (simp, erule impE)
  apply (meson rtrancl_trans subcls1_confluent)
 apply blast
apply simp
done

lemma subcls_of_Obj_acyclic1: "P \<turnstile> C \<preceq>\<^sup>* Object \<Longrightarrow> (C, C) \<notin> (subcls1 P)\<^sup>+"
by (metis r_into_rtrancl subcls1.simps subcls_of_Obj_acyclic subcls_self_superclass tranclD)

lemma subcls_of_Obj: "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* Object; P \<turnstile> C \<preceq>\<^sup>* D \<rbrakk> \<Longrightarrow> P \<turnstile> D \<preceq>\<^sup>* Object"
apply (drule subcls_confluent, simp+)
apply (erule disjE, simp+)
done


(***********Class/subcls finiteness properties*****************)

(* HERE: move when done *)
(* lemma map_of_list_finite: "finite {x. map_of (l::('a \<times> 'b) list) x \<noteq> None}"
by (metis dom_def finite_dom_map_of) *)
lemma class_set_finite: "finite {C. class P C \<noteq> None}"
 by (simp only: class_def, metis dom_def finite_dom_map_of)

lemma subcls_None_unique:
 "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* C'; P \<turnstile> C \<preceq>\<^sup>* C''; C' \<noteq> C''; class P C' = None \<rbrakk>
\<Longrightarrow>
  class P C'' \<noteq> None"
by (metis converse_rtranclE option.distinct(1) subcls1.cases subcls_confluent)

lemma subcls_set_finite: "finite {C'. P \<turnstile> C \<preceq>\<^sup>* C'}"
apply (case_tac "\<exists>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<and> class P C' = None")
 apply clarify
 apply (subgoal_tac "{C'. P \<turnstile> C \<preceq>\<^sup>* C'} \<subseteq> {C. class P C \<noteq> None} \<union> {C'}")
  prefer 2
  using Un_insert_right insertCI mem_Collect_eq subcls_None_unique apply fastforce
 using class_set_finite finite_subset apply fastforce
apply (subgoal_tac "{C'. P \<turnstile> C \<preceq>\<^sup>* C'} \<subseteq> {C. class P C \<noteq> None}")
 prefer 2 apply fastforce
using class_set_finite finite_subset apply fastforce
done

(***********Cyclic structure*****************)

lemma cyclic_subcls:
"\<lbrakk> (C, C) \<in> (subcls1 P)\<^sup>+; P \<turnstile> C \<preceq>\<^sup>* C' \<rbrakk>
 \<Longrightarrow> P \<turnstile> C' \<preceq>\<^sup>* C"
apply (cut_tac P = "\<lambda>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<longrightarrow> P \<turnstile> C' \<preceq>\<^sup>* C" in rtrancl_induct, simp+)
 apply (metis single_valuedD subcls1_confluent subcls1_single_valued tranclD)
apply simp
done

(* HERE: might move this def elsewhere *)
definition cyclic_above :: "'m prog \<Rightarrow> cname \<Rightarrow> bool" ("_ cyclicAbove _"  [71,71] 70) where
"P cyclicAbove C = (\<exists>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<and> (C', C') \<in> (subcls1 P)\<^sup>+)"

lemma subcls_cyclic_above:
 "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* C' \<rbrakk> \<Longrightarrow> P cyclicAbove C = P cyclicAbove C'"
apply rule
 apply (meson cyclic_above_def cyclic_subcls subcls_confluent)
by (meson cyclic_above_def rtrancl_trans)

lemma cyclic_above_not_subcls_of_Obj:
 "\<lbrakk> P cyclicAbove C \<rbrakk> \<Longrightarrow> \<not>P \<turnstile> C \<preceq>\<^sup>* Object"
using cyclic_above_def subcls_of_Obj subcls_of_Obj_acyclic1 by blast

lemma cyclic_above_classes_exist:
 "\<lbrakk> P cyclicAbove C \<rbrakk>
 \<Longrightarrow>
  \<forall>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>D rest. class P C' = Some (D,rest))"
apply (clarsimp simp add: cyclic_above_def)
apply (subgoal_tac "P \<turnstile> C'a \<preceq>\<^sup>* C'")
 prefer 2
 using cyclic_subcls subcls_confluent apply blast
apply (meson rtrancl_trancl_trancl subcls1D tranclD)
done

lemma cyclic_aboveD:
 "\<lbrakk>  P cyclicAbove C \<rbrakk>
 \<Longrightarrow> (\<forall>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>D rest. class P C' = Some (D,rest))) \<and> \<not>P \<turnstile> C \<preceq>\<^sup>* Object"
using cyclic_above_classes_exist cyclic_above_not_subcls_of_Obj by blast

lemma not_cyclic_above_subcls_set_strict_subset:
 "\<lbrakk> \<not>P cyclicAbove C; P \<turnstile> C \<preceq>\<^sup>* C'; C \<noteq> C' \<rbrakk>
 \<Longrightarrow>
  {C''. P \<turnstile> C' \<preceq>\<^sup>* C''} \<subset> {C'. P \<turnstile> C \<preceq>\<^sup>* C'}"
apply rule
 apply fastforce
apply (subgoal_tac "C \<notin> {C''. P \<turnstile> C' \<preceq>\<^sup>* C''}")
 prefer 2
 apply (metis CollectD cyclic_above_def rtranclD rtrancl_trancl_trancl)
apply fastforce
done

lemma not_cyclic_above_ends:
 "\<lbrakk> \<not>P cyclicAbove C \<rbrakk> \<Longrightarrow> \<exists>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<and> {C''. P \<turnstile> C' \<preceq>\<^sup>* C''} = {C'}"
apply (cut_tac A = "{C'. P \<turnstile> C \<preceq>\<^sup>* C'}" and
  P = "\<lambda>B. (\<exists>C. \<not> P cyclicAbove C \<and> B = {C'. P \<turnstile> C \<preceq>\<^sup>* C'})
    \<longrightarrow> (\<exists>C C'. B = {C'. P \<turnstile> C \<preceq>\<^sup>* C'} \<and> P \<turnstile> C \<preceq>\<^sup>* C' \<and> {C''. P \<turnstile> C' \<preceq>\<^sup>* C''} = {C'})"
 in finite_psubset_induct)
  apply (rule subcls_set_finite)
 defer
apply blast
(* deferred subgoal from induction *)
apply clarsimp
apply (subgoal_tac "\<forall>B. B \<subset> {C'. P \<turnstile> Ca \<preceq>\<^sup>* C'} \<longrightarrow>
                ((\<exists>C. \<not> P cyclicAbove C \<and> B = {C'. P \<turnstile> C \<preceq>\<^sup>* C'}) \<longrightarrow>
                (\<exists>C. B = {C'. P \<turnstile> C \<preceq>\<^sup>* C'} \<and> (\<exists>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<and> {C''. P \<turnstile> C' \<preceq>\<^sup>* C''} = {C'})))")
 prefer 2 apply simp
apply (rule_tac x = Ca in exI, simp)
apply (case_tac "{C''. P \<turnstile> Ca \<preceq>\<^sup>* C''} = {Ca}", fastforce)
apply (subgoal_tac "\<exists>Caa. P \<turnstile> Ca \<preceq>\<^sup>* Caa \<and> Ca \<noteq> Caa")
 prefer 2 apply blast
apply clarify
apply (erule_tac x = "{C'. P \<turnstile> Caa \<preceq>\<^sup>* C'}" in allE)
 apply (erule impE, rule not_cyclic_above_subcls_set_strict_subset, simp+)
 apply (erule impE, rule_tac x = Caa in exI, simp add: subcls_cyclic_above)
apply clarsimp
apply (rule_tac x = C' in exI, simp)
apply (metis mem_Collect_eq r_r_into_trancl rtrancl_trancl_absorb)
done

lemma not_cyclic_no_super_Obj_or_None:
 "\<lbrakk> (C, C) \<notin> (subcls1 P)\<^sup>+; {C'. P \<turnstile> C \<preceq>\<^sup>* C'} = {C} \<rbrakk>
 \<Longrightarrow>
   C = Object \<or> class P C = None"
apply (case_tac "C = Object", simp+)
apply (rule classical, clarsimp)
using subcls1.subcls1I by fastforce

lemma not_cyclic_above_ends_in_Obj_or_None:
 "\<lbrakk> \<not>P cyclicAbove C \<rbrakk>
 \<Longrightarrow>
   \<exists>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<and> (C' = Object \<or> class P C' = None)"
apply (frule not_cyclic_above_ends, clarify)
apply (rule_tac x = C' in exI, simp)
apply (rule not_cyclic_no_super_Obj_or_None)
 apply (frule subcls_cyclic_above, simp, simp add: cyclic_above_def)
apply simp
done

lemma not_cyclic_above_and_exists_subcls_Obj:
 "\<lbrakk> \<forall>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>D rest. class P C' = Some (D,rest));
    \<not>P cyclicAbove C \<rbrakk>
 \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* Object"
 by (drule not_cyclic_above_ends_in_Obj_or_None, fastforce)

lemma cyclic_aboveI:
 "\<lbrakk> \<forall>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>D rest. class P C' = Some (D,rest));
    \<not>P \<turnstile> C \<preceq>\<^sup>* Object \<rbrakk>
 \<Longrightarrow> P cyclicAbove C"
apply (rule classical, simp (no_asm_simp))
apply (drule not_cyclic_above_and_exists_subcls_Obj, simp+)
done

lemma cyclic_above_equiv:
 "P cyclicAbove C
     = ((\<forall>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>D rest. class P C' = Some (D,rest))) \<and> (\<not>P \<turnstile> C \<preceq>\<^sup>* Object))"
apply (rule iffI)
 using cyclic_aboveD apply blast
using cyclic_aboveI apply blast
done


(***)
(* HERE: should be moved somewhere else *)
(* A bit of preilminary theory about some sets of classes defined using the subclass relation *)

abbreviation classes_above :: "'m prog \<Rightarrow> cname \<Rightarrow> cname set" where
"classes_above P c \<equiv> { cn. P \<turnstile> c \<preceq>\<^sup>* cn }"

abbreviation classes_strict_above :: "'m prog \<Rightarrow> cname \<Rightarrow> cname set" where
"classes_strict_above P c \<equiv> { cn. (c, cn) \<in> (subcls1 P)\<^sup>+ }"

abbreviation classes_between :: "'m prog \<Rightarrow> cname \<Rightarrow> cname \<Rightarrow> cname set" where
"classes_between P c d \<equiv> { cn. (P \<turnstile> c \<preceq>\<^sup>* cn \<and> P \<turnstile> cn \<preceq>\<^sup>* d) (* \<or> (P \<turnstile> d \<preceq>\<^sup>* cn \<and> P \<turnstile> cn \<preceq>\<^sup>* c)*) }"

lemma classes_strict_above_classes_above_supercls:
  "\<lbrakk> P \<turnstile> C \<prec>\<^sup>1 C' \<rbrakk> \<Longrightarrow> classes_strict_above P C = classes_above P C'"
apply rule
 apply (rule, clarify)
 apply (metis single_valuedD subcls1_single_valued tranclD)
apply (rule, clarify, simp)
done

lemma classes_between_above_equiv:
 "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* Object; P \<turnstile> C \<preceq>\<^sup>* D \<or> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
 \<Longrightarrow> classes_between P C D = classes_above P C - classes_strict_above P D"
apply rule
 apply (clarify, rule, simp)
 apply (case_tac "x = D")
  apply (frule_tac D = D in subcls_of_Obj, simp)
  apply (simp add: subcls_of_Obj_acyclic1)
 apply (frule_tac D = x in subcls_of_Obj, simp)
 apply (drule_tac C = x in subcls_of_Obj_acyclic, simp, clarsimp)
 apply (simp add: rtrancl_eq_or_trancl)
apply clarify
apply (erule disjE)
 apply (drule_tac C' = x and C'' = D in subcls_confluent, simp)
 apply (erule disjE, simp)
 apply (simp add: rtrancl_eq_or_trancl)
apply (drule_tac x = D and z = x in rtrancl_trans, simp)
apply (simp add: rtrancl_eq_or_trancl)
done

(* HERE: only true if the class structure for the class isn't cyclic - which is true if it is a
 subclass of Object *)
(* may modify this to use "not cyclic above" instead, since that's less of an assumption - but
 this isn't used anyway *)
lemma "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* Object \<rbrakk> \<Longrightarrow> classes_between P C C = { C }"
apply rule
 using subcls_of_Obj_acyclic apply fastforce
apply simp
done


end