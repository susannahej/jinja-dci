(*  Title:      Jinja/Common/ClassesAbove.thy
    Author:    Susannah Mansky, UIUC 2016
*)

(* HERE: might integrate below into other files *)

(* HERE: write a better .thy description *)
section {* Theory around the classes above a class in the class structure,
 in particular noting that if they have not changed, then much of what that
 class sees (methods, fields) stays the same. *}

theory ClassesAbove
imports ClassesBetween
begin

lemma classes_between_classes_above_subset:
 "classes_between P C C' \<subseteq> classes_above P C"
 by blast

lemma classes_above_unchanged_classes_between_unchanged:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {} \<rbrakk>
 \<Longrightarrow> classes_between P C C' \<inter> classes_changed P P' = {}"
by blast

(**)

lemma classes_above_unchanged:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {}; P \<turnstile> C \<preceq>\<^sup>* C' \<rbrakk>
  \<Longrightarrow> class P C' = class P' C'"
 by (drule classes_unchanged_set, simp)

lemma classes_above_unchanged_subset:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {} \<rbrakk>
  \<Longrightarrow> classes_above P C \<subseteq> classes_above P' C"
apply (frule classes_unchanged_set, simp)
apply rule
apply clarify
apply (cut_tac P = "\<lambda>x. P \<turnstile> C \<preceq>\<^sup>* x \<longrightarrow> P' \<turnstile> C \<preceq>\<^sup>* x" in rtrancl_induct, simp+)
 apply clarify
 apply (subgoal_tac "P' \<turnstile> y \<prec>\<^sup>1 z")
  prefer 2
  apply (erule_tac x = y in allE, erule impE, force)
  apply (drule same_class_same_superclass, simp, fastforce)
 apply fastforce
apply simp
done

lemma classes_above_unchanged_subcls:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {}; P \<turnstile> C \<preceq>\<^sup>* C' \<rbrakk>
   \<Longrightarrow> P' \<turnstile> C \<preceq>\<^sup>* C'"
apply (drule classes_above_unchanged_subset)
apply (force)
done

lemma classes_above_unchanged_subset2:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {} (*; P' \<turnstile> C \<preceq>\<^sup>* Object*) \<rbrakk>
  \<Longrightarrow> classes_above P' C \<subseteq> classes_above P C"
apply (frule classes_unchanged_set, simp)
apply rule
apply clarify
apply (cut_tac P = "\<lambda>x. P' \<turnstile> C \<preceq>\<^sup>* x \<longrightarrow> P \<turnstile> C \<preceq>\<^sup>* x" in rtrancl_induct, simp+)
 apply clarify
 apply (metis (no_types, hide_lams) converse_rtrancl_into_rtrancl r_into_rtrancl rtrancl_idemp
   same_class_same_superclass)
apply simp
done

lemma classes_above_unchanged_subcls2:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {}; P' \<turnstile> C \<preceq>\<^sup>* C' \<rbrakk>
   \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* C'"
apply (drule classes_above_unchanged_subset2)
apply (force)
done

lemma classes_above_unchanged_same_set:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {} \<rbrakk>
  \<Longrightarrow> classes_above P C = classes_above P' C"
apply rule
 apply (rule classes_above_unchanged_subset, simp)
apply (rule classes_above_unchanged_subset2, simp+)
done

lemma classes_above_classes_changed_sym:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {} \<rbrakk>
 \<Longrightarrow> classes_above P' C \<inter> classes_changed P' P = {}"
apply (frule classes_above_unchanged_same_set)
apply (cut_tac P = P and P' = P' in classes_changed_sym)
apply simp
done

lemma classes_above_unchanged_subcls_trans:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {};
    P \<turnstile> C \<preceq>\<^sup>* C';
    P \<turnstile> C' \<preceq>\<^sup>* C'' \<rbrakk>
 \<Longrightarrow> P' \<turnstile> C' \<preceq>\<^sup>* C''"
by (smt classes_above_unchanged_subcls disjoint_iff_not_equal mem_Collect_eq rtrancl_trans)


(* classes_strict_above *)

lemma classes_strict_above_unchanged_same_set:
 "\<lbrakk> classes_strict_above P C \<inter> classes_changed P P' = {}; P \<turnstile> C \<prec>\<^sup>1 C'; P' \<turnstile> C \<prec>\<^sup>1 C' \<rbrakk>
  \<Longrightarrow> classes_strict_above P C = classes_strict_above P' C"
apply (drule classes_strict_above_classes_above_supercls)+
apply simp
apply (rule classes_above_unchanged_same_set, simp)
done

(*****************************Methods*********************************)

lemma classes_above_unchanged_sees_methods_exists:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {};
     P \<turnstile> C sees_methods Mm \<rbrakk>
 \<Longrightarrow> \<exists>Mm. P' \<turnstile> C sees_methods Mm"
apply (frule sees_methodsD, clarsimp)
apply (rule subcls_Obj_sees_methods_exists)
 apply (frule classes_above_unchanged_subcls, simp+)
by (simp add: classes_unchanged_set)

lemma classes_unchanged_sees_methods_same:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {}; P \<turnstile> C sees_methods Mm \<rbrakk>
  \<Longrightarrow> P' \<turnstile> C sees_methods Mm"
apply (drule classes_unchanged_set)
apply (cut_tac Pa = "\<lambda>C Mm. (\<forall>x. P \<turnstile> C \<preceq>\<^sup>* x \<longrightarrow> (class P x = class P' x))
 \<longrightarrow> P' \<turnstile> C sees_methods Mm" in Methods.induct, simp)
  apply (clarify, erule_tac x = Object in allE, simp)
  apply (simp add: sees_methods_Object)
 apply clarify
 apply (erule impE)
  apply clarify
  apply (drule_tac C = Ca in subcls1I, simp)
  apply (erule_tac x = x in allE)
  apply (erule impE, simp+)
 apply (erule_tac x = Ca in allE, simp)
 apply (rule sees_methods_rec, simp+)
done

lemma classes_unchanged_sees_methods_same2:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {}; P' \<turnstile> C sees_methods Mm \<rbrakk>
  \<Longrightarrow> P \<turnstile> C sees_methods Mm"
apply (drule classes_above_classes_changed_sym)
apply (rule classes_unchanged_sees_methods_same, simp+)
done

lemma classes_unchanged_sees_methods_dne:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {} \<rbrakk>
 \<Longrightarrow> (\<forall>Mm. \<not> P \<turnstile> C sees_methods Mm) = (\<forall>Mm. \<not> P' \<turnstile> C sees_methods Mm)"
apply rule
 apply (rule classical, clarsimp)
 apply (drule classes_unchanged_sees_methods_same2)
 apply simp+
apply (rule classical, clarsimp)
 apply (drule classes_unchanged_sees_methods_same)
 apply simp+
done

lemma classes_unchanged_sees_method_dne:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {};
     \<not>(\<exists>Ts T m D b. P \<turnstile> C sees M,b: Ts\<rightarrow>T = m in D) \<rbrakk>
  \<Longrightarrow> \<not>(\<exists>Ts T m D b. P' \<turnstile> C sees M,b: Ts\<rightarrow>T = m in D)"
apply (simp add: sees_methods_dne_equiv)
apply (erule disjE)
 apply (rule disjI1)
 apply (simp add: classes_unchanged_sees_methods_dne)
apply (rule disjI2, clarsimp)
apply (drule classes_unchanged_sees_methods_same, simp)
apply force
done

lemma classes_unchanged_sees_method_dne2:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {};
     \<not>(\<exists>Ts T m D b. P' \<turnstile> C sees M,b: Ts\<rightarrow>T = m in D) \<rbrakk>
  \<Longrightarrow> \<not>(\<exists>Ts T m D b. P \<turnstile> C sees M,b: Ts\<rightarrow>T = m in D)"
apply (drule classes_above_classes_changed_sym)
apply (frule classes_unchanged_sees_method_dne, simp+)
done

lemma classes_unchanged_sees_method_dne3:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {};
     \<not>(\<exists>m D. P \<turnstile> C sees M,b: Ts\<rightarrow>T = m in D) \<rbrakk>
  \<Longrightarrow> \<not>(\<exists>m D. P' \<turnstile> C sees M,b: Ts\<rightarrow>T = m in D)"
apply (simp add: sees_methods_dne_equiv2)
apply (erule disjE)
 apply (rule disjI1)
 apply (simp add: classes_unchanged_sees_methods_dne)
apply (rule disjI2, clarsimp)
apply (drule classes_unchanged_sees_methods_same, simp)
apply (rule_tac x = Mm in exI, simp)
done


lemma classes_above_unchanged_sees_same_method:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {};
     P \<turnstile> C sees M,b: Ts\<rightarrow>T = m in C' \<rbrakk>
  \<Longrightarrow> P' \<turnstile> C sees M,b: Ts\<rightarrow>T = m in C'"
apply (frule sees_method_decl_above)
apply (clarsimp simp add: Method_def)
apply (frule classes_above_unchanged_sees_methods_exists, simp)
using classes_unchanged_sees_method_same by blast


lemma classes_above_unchanged_sees_same_method2:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {};
     P' \<turnstile> C sees M,b: Ts\<rightarrow>T = m in C' \<rbrakk>
  \<Longrightarrow> P \<turnstile> C sees M,b: Ts\<rightarrow>T = m in C'"
apply (drule classes_above_classes_changed_sym)
apply (rule classes_above_unchanged_sees_same_method, simp+)
done

lemma classes_above_unchanged_method_same:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {} \<rbrakk>
 \<Longrightarrow> method P C M = method P' C M"
apply (simp add: method_def)
apply (case_tac "\<exists>Ts T m D b. P \<turnstile> C sees M,b :  Ts\<rightarrow>T = m in D")
 apply (clarify, frule classes_above_unchanged_sees_same_method, simp)
 apply (metis method_def method_def2)
apply (subgoal_tac "\<not>(\<exists>Ts T m D b. P' \<turnstile> C sees M,b :  Ts\<rightarrow>T = m in D)")
 prefer 2
 apply (rule classical, clarify, frule classes_above_unchanged_sees_same_method2, simp+)
done

(********************* Fields ************************)


lemma classes_above_unchanged_has_fields_exists:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {};
     P \<turnstile> C has_fields FDTs \<rbrakk>
 \<Longrightarrow> \<exists>FDTs. P' \<turnstile> C has_fields FDTs"
apply (frule has_fieldsD, clarsimp)
apply (rule subcls_Obj_has_fields_exists)
 apply (frule classes_above_unchanged_subcls, simp+)
by (simp add: classes_unchanged_set)

lemma classes_unchanged_has_fields_same:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {}; P \<turnstile> C has_fields FDTs \<rbrakk>
  \<Longrightarrow> P' \<turnstile> C has_fields FDTs"
apply (drule classes_unchanged_set)
apply (cut_tac Pa = "\<lambda>C FDTs. (\<forall>x. P \<turnstile> C \<preceq>\<^sup>* x \<longrightarrow> (class P x = class P' x))
 \<longrightarrow> P' \<turnstile> C has_fields FDTs" in Fields.induct, simp)
  apply clarify
  apply (erule impE)
   apply clarify
   apply (drule_tac C = Ca in subcls1I, simp)
   apply (erule_tac x = x in allE)
   apply (erule impE, simp+)
  apply (erule_tac x = Ca in allE, simp)
  apply (rule has_fields_rec, simp+)
 apply (clarify, erule_tac x = Object in allE, simp)
 apply (rule has_fields_Object, rule sym, simp+)
done

lemma classes_unchanged_has_fields_dne:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {} \<rbrakk>
 \<Longrightarrow> (\<forall>FDTs. \<not> P \<turnstile> C has_fields FDTs) = (\<forall>FDTs. \<not> P' \<turnstile> C has_fields FDTs)"
apply rule
 apply (rule classical, clarsimp)
 apply (frule classes_above_unchanged_same_set, cut_tac P = P and P' = P' in classes_changed_sym)
 apply simp
 apply (drule classes_unchanged_has_fields_same)
 apply simp+
apply (rule classical, clarsimp)
 apply (drule classes_unchanged_has_fields_same)
 apply simp+
done

lemma classes_unchanged_sees_field_dne:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {};
     \<not>(\<exists>T D b. P \<turnstile> C sees F,b: T in D) \<rbrakk>
  \<Longrightarrow> \<not>(\<exists>T D b. P' \<turnstile> C sees F,b: T in D)"
apply (simp add: has_fields_dne_equiv)
apply (erule disjE)
 apply (rule disjI1)
 apply (simp add: classes_unchanged_has_fields_dne)
apply (rule disjI2, clarsimp)
apply (drule classes_unchanged_has_fields_same, simp)
apply force
done

lemma classes_unchanged_sees_field_dne2:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {};
     \<not>(\<exists>T D b. P' \<turnstile> C sees F,b: T in D) \<rbrakk>
  \<Longrightarrow> \<not>(\<exists>T D b. P \<turnstile> C sees F,b: T in D)"
apply (drule classes_above_classes_changed_sym)
apply (frule classes_unchanged_sees_field_dne, simp+)
done

lemma classes_above_unchanged_has_same_field:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {};
    P \<turnstile> C has F,b:t in C' \<rbrakk>
   \<Longrightarrow> P' \<turnstile> C has F,b:t in C'"
apply (clarsimp simp add: has_field_def)
apply (frule classes_above_unchanged_has_fields_exists, simp)
using classes_unchanged_has_fields_same by blast

lemma classes_above_unchanged_has_same_field2:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {};
     P' \<turnstile> C has F,b:t in C' \<rbrakk>
  \<Longrightarrow> P \<turnstile> C has F,b:t in C'"
apply (drule classes_above_classes_changed_sym)
apply (rule classes_above_unchanged_has_same_field, simp+)
done

lemma classes_above_unchanged_sees_same_field:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {};
    P \<turnstile> C sees F,b:t in C' \<rbrakk>
   \<Longrightarrow> P' \<turnstile> C sees F,b:t in C'"
apply (clarsimp simp add: sees_field_def)
apply (frule classes_above_unchanged_has_fields_exists, simp)
using classes_unchanged_has_fields_same by blast

lemma classes_above_unchanged_sees_same_field2:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {};
     P' \<turnstile> C sees F,b:t in C' \<rbrakk>
  \<Longrightarrow> P \<turnstile> C sees F,b:t in C'"
apply (drule classes_above_classes_changed_sym)
apply (rule classes_above_unchanged_sees_same_field, simp+)
done

lemma classes_above_unchanged_field_same:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {} \<rbrakk>
 \<Longrightarrow> field P C F = field P' C F"
apply (simp add: field_def)
apply (case_tac "\<exists>T D b. P \<turnstile> C sees F,b : T in D")
 apply (clarify, frule classes_above_unchanged_sees_same_field, simp)
 apply (metis field_def field_def2)
apply (subgoal_tac "\<not>(\<exists>T D b. P' \<turnstile> C sees F,b : T in D)")
 prefer 2
 apply (rule classical, clarify, frule classes_above_unchanged_sees_same_field2, simp+)
done

lemma classes_unchanged_fields_same:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {} \<rbrakk>
 \<Longrightarrow>
  fields P C = fields P' C"
apply (simp add: fields_def)
apply (case_tac "\<exists>FDTs. P \<turnstile> C has_fields FDTs")
 apply clarify
 apply (drule classes_unchanged_has_fields_same, simp)
 apply (metis fields_def fields_def2)
apply (drule classes_unchanged_has_fields_dne, simp)
done

lemma classes_unchanged_ifields_same:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {} \<rbrakk>
 \<Longrightarrow>
  ifields P C = ifields P' C"
 by (simp add: ifields_def classes_unchanged_fields_same)

lemma classes_unchanged_blank_same:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {} \<rbrakk>
 \<Longrightarrow>
  blank P C = blank P' C"
 by (simp add: blank_def classes_unchanged_ifields_same)


lemma classes_unchanged_isfields_same:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {} \<rbrakk>
 \<Longrightarrow>
  isfields P C = isfields P' C"
 by (simp add: isfields_def classes_unchanged_fields_same)

lemma classes_unchanged_sblank_same:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {} \<rbrakk>
 \<Longrightarrow>
  sblank P C = sblank P' C"
 by (simp add: sblank_def classes_unchanged_isfields_same)


(* overrides *)

lemma classes_above_subset:
 "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* C' \<rbrakk>
 \<Longrightarrow> classes_above P C' \<subseteq> classes_above P C"
 by auto
(**)

(********
lemma classes_unchanged_overrides_dne:
 "\<lbrakk> (classes_above P C' \<union> classes_between P C D) \<inter> classes_changed P P' = {};
    P \<turnstile> C \<preceq>\<^sup>* D; P \<turnstile> D \<preceq>\<^sup>* Object; \<exists>D' fs ms. class P Object = \<lfloor>(D', fs, ms)\<rfloor>;
    \<not>(\<exists> m' D'. P \<turnstile> C', m', D' overrides C, M = m in D : Ts \<rightarrow> T, static b) \<rbrakk>
 \<Longrightarrow> \<not>(\<exists> m' D'. P' \<turnstile> C', m', D' overrides C, M = m in D : Ts \<rightarrow> T, static b)"
apply (clarsimp simp add: overrides_dne_equiv)
apply (erule impE)
 apply (rule classes_unchanged_sees_same_method2, blast, simp+)
apply (erule notE)
apply (cut_tac classes_above_unchanged_same_set, blast, blast)
done

lemma classes_above_unchanged_overrides_dne:
 "\<lbrakk> (classes_above P C' \<union> classes_above P C) \<inter> classes_changed P P' = {};
    \<not>(\<exists> m' D'. P \<turnstile> C', m', D' overrides C, M = m in D : Ts \<rightarrow> T, static b) \<rbrakk>
 \<Longrightarrow> \<not>(\<exists> m' D'. P' \<turnstile> C', m', D' overrides C, M = m in D : Ts \<rightarrow> T, static b)"
apply (clarsimp simp add: overrides_dne_equiv)
apply (erule impE)
 apply (rule classes_above_unchanged_sees_same_method2, blast, simp)
apply (erule notE)
apply (cut_tac classes_above_unchanged_same_set, blast, blast)
done

(* HERE: some of the subgoals here should probably come more directly from theory
 on overrides not yet developed *)
lemma classes_above_unchanged_overrides_same:
 "\<lbrakk> classes_above P C' \<inter> classes_changed P P' = {};
    P \<turnstile> C', m', D' overrides C, M = m in D : Ts \<rightarrow> T, static b \<rbrakk>
 \<Longrightarrow> P' \<turnstile> C', m', D' overrides C, M = m in D : Ts \<rightarrow> T, static b"
apply (subgoal_tac "classes_between P C' D \<inter> classes_changed P P' = {}")
 prefer 2 apply (rule classes_above_unchanged_classes_between_unchanged, simp)
apply (subgoal_tac "P \<turnstile> D \<preceq>\<^sup>* Object")
 prefer 2 apply (clarsimp simp add: Overrides_def sees_method_sub_Obj2)
apply (subgoal_tac "P \<turnstile> C' \<preceq>\<^sup>* D")
 prefer 2 apply (meson Overrides_def overrides_subcls rtrancl_trans sees_method_decl_above)
apply (subgoal_tac "P' \<turnstile> D \<preceq>\<^sup>* Object")
 prefer 2 apply (rule classes_above_unchanged_subcls_trans, simp+)
apply (subgoal_tac "P \<turnstile> C' \<preceq>\<^sup>* Object")
 prefer 2 apply auto[1]
apply (subgoal_tac "\<exists>D' fs ms. class P Object = \<lfloor>(D', fs, ms)\<rfloor>")
 prefer 2 apply (meson Overrides_def sees_method_Object_exists)
apply (subgoal_tac "\<exists>D' fs ms. class P' Object = \<lfloor>(D', fs, ms)\<rfloor>")
 prefer 2 apply (simp add: classes_unchanged_set)
apply (rule classes_unchanged_overrides_same, simp+)
done
***************)

(******)
(* checkcast_class_collect *)

lemma checkcast_class_collect_unchanged_same_set:
 "\<lbrakk> checkcast_class_collect P C h v \<inter> classes_changed P P' = {} (*;
    v \<noteq> Null \<longrightarrow> P' \<turnstile> C \<preceq>\<^sup>* Object *) \<rbrakk>
   \<Longrightarrow> checkcast_class_collect P C h v = checkcast_class_collect P' C h v"
apply (simp add: checkcast_class_collect_def)
apply (case_tac "v = Null", simp)
apply simp
apply (frule classes_above_unchanged_same_set, simp)
done

lemma classes_unchanged_cast_ok_true:
 "\<lbrakk> checkcast_class_collect P C h v \<inter> classes_changed P P' = {};
     (* v \<noteq> Null \<longrightarrow> P' \<turnstile> C \<preceq>\<^sup>* Object;*)
     cast_ok P C h v = b \<rbrakk>
   \<Longrightarrow> cast_ok P' C h v = b"
apply (simp add: cast_ok_def checkcast_class_collect_def)
apply (case_tac "v = Null", simp)
apply simp
apply (cut_tac P = P in classes_above_unchanged_same_set, simp)
apply blast
done

lemma classes_unchanged_cast_ok_false:
 "\<lbrakk> checkcast_class_collect P C h v \<inter> classes_changed P P' = {};
     (* P' \<turnstile> C \<preceq>\<^sup>* Object; *)
     \<not> cast_ok P C h v = b \<rbrakk>
   \<Longrightarrow> \<not> cast_ok P' C h v = b"
apply (simp add: cast_ok_def checkcast_class_collect_def)
apply (case_tac "v = Null", simp)
apply simp
apply (cut_tac P = P in classes_above_unchanged_same_set, simp)
apply blast
done

(****)

lemma classes_unchanged_start_heap_same:
 "(\<Union>C \<in> sys_xcpts. classes_above P C) \<inter> classes_changed P P' = {}
  \<Longrightarrow> start_heap P = start_heap P'"
apply (simp add: start_heap_def)
apply (subgoal_tac "\<forall>C \<in> sys_xcpts. blank P C = blank P' C")
 prefer 2
 apply clarsimp
 apply (rule classes_unchanged_blank_same, fastforce)
apply simp
done

(****)

lemma classes_changed_all_still_subcls:
 "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* C';
    \<forall>C \<in> classes_changed P P'. P' \<turnstile> C \<preceq>\<^sup>* C' \<rbrakk>
\<Longrightarrow>
   P' \<turnstile> C \<preceq>\<^sup>* C'"
apply (case_tac "classes_above P C \<inter> classes_changed P P' = {}")
 using classes_above_unchanged_subcls apply blast
by (smt classes_above_unchanged_subcls2 classes_changed_sym disjoint_iff_not_equal
   mem_Collect_eq rtrancl_trans)


(* HERE: unused *)
(*
(* is this exactly what we need? *)
thm sees_method_decl_mono
lemma
 "\<lbrakk> P \<turnstile> C', m', D' overrides C, M = m in D : Ts \<rightarrow> T, static b  \<rbrakk>
 \<Longrightarrow> C' = C \<or> P \<turnstile> D' \<preceq>\<^sup>* C"
oops

lemma
 "\<lbrakk> P \<turnstile> C', m', D' overrides C, M = m in D : Ts \<rightarrow> T, static b \<rbrakk>
 \<Longrightarrow> P \<turnstile> D \<preceq>\<^sup>* Object"
oops
*)

(* HERE: do we need/want this? *)
(*
lemma classes_unchanged_checkcast_not_null_subcls:
 "\<lbrakk> checkcast_class_collect P C h v \<inter> classes_changed P P' = {};
    \<forall>C \<in> classes_changed P P'. P' \<turnstile> C \<preceq>\<^sup>* C' \<rbrakk>
\<Longrightarrow>
   v \<noteq> Null \<longrightarrow> P' \<turnstile> C \<preceq>\<^sup>* C'"
apply (simp add: checkcast_class_collect_def)
apply (case_tac "v = Null", simp)
apply simp
apply (case_tac "P \<turnstile> cname_of h (the_Addr v) \<preceq>\<^sup>* C")
 apply simp
 apply (subgoal_tac "P \<turnstile> C \<preceq>\<^sup>* C'")
  prefer 2
  defer
 defer
apply simp
oops
*)

end