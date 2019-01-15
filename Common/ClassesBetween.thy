(*  Title:      Jinja/Common/ClassesBetween.thy
    Author:    Susannah Mansky, UIUC 2016
*)

section {* Theory around the classes between two class in the class structure,
 in particular noting that if they have not changed, then what the
 subclass sees (methods, fields) found between the two stays the same. *}

theory ClassesBetween
imports ClassesChanged MethodsAndFields
begin


lemma classes_between_subset_below:
 "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* C'; P \<turnstile> C' \<preceq>\<^sup>* C'' \<rbrakk>
 \<Longrightarrow> classes_between P C C' \<subseteq> classes_between P C C''"
 by auto

lemma classes_between_subset_above:
 "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* C'; P \<turnstile> C' \<preceq>\<^sup>* C'' \<rbrakk>
 \<Longrightarrow> classes_between P C' C'' \<subseteq> classes_between P C C''"
 by auto

lemma classes_between_subset_between:
 "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* C'; P \<turnstile> C' \<preceq>\<^sup>* C''; P \<turnstile> C'' \<preceq>\<^sup>* C''' \<rbrakk>
 \<Longrightarrow> classes_between P C' C'' \<subseteq> classes_between P C C'''"
 by auto


(**)

lemma classes_between_unchanged:
 "\<lbrakk> classes_between P C C' \<inter> classes_changed P P' = {}; P \<turnstile> C \<preceq>\<^sup>* C''; P \<turnstile> C'' \<preceq>\<^sup>* C' \<rbrakk>
  \<Longrightarrow> class P C'' = class P' C''"
 by (drule classes_unchanged_set, simp)

lemma classes_between_unchanged_subset:
 "\<lbrakk> classes_between P C C' \<inter> classes_changed P P' = {} \<rbrakk>
  \<Longrightarrow> classes_between P C C' \<subseteq> classes_between P' C C'"
apply (frule classes_unchanged_set, simp)
apply rule
(* \<Rightarrow> *)
apply clarify
apply (cut_tac P = "\<lambda>x. P \<turnstile> x \<preceq>\<^sup>* C' \<longrightarrow> P' \<turnstile> C \<preceq>\<^sup>* x" in rtrancl_induct, simp+)
 apply clarify
 apply (subgoal_tac "P' \<turnstile> y \<prec>\<^sup>1 z")
  prefer 2
  apply (erule_tac x = y in allE, erule impE, force) apply (erule impE, force)
  apply (drule same_class_same_superclass, simp, fastforce)
 apply (erule impE, fastforce)
 apply fastforce
apply simp
apply (cut_tac a = x and b = C' and P = "\<lambda>x. P \<turnstile> C \<preceq>\<^sup>* x \<longrightarrow> P' \<turnstile> x \<preceq>\<^sup>* C'" in converse_rtrancl_induct, simp+)
 apply clarify
 apply (subgoal_tac "P' \<turnstile> y \<prec>\<^sup>1 z")
  prefer 2
  apply (erule_tac x = y in allE, erule impE, force) apply (erule impE, force)
  apply (drule same_class_same_superclass, simp, fastforce)
 apply (erule impE, fastforce)
 apply fastforce
apply simp
done

lemma classes_between_unchanged_subcls:
 "\<lbrakk> classes_between P C C' \<inter> classes_changed P P' = {}; P \<turnstile> C \<preceq>\<^sup>* C' \<rbrakk>
   \<Longrightarrow> P' \<turnstile> C \<preceq>\<^sup>* C'"
apply (drule classes_between_unchanged_subset)
apply (force)
done

(* this direction requires a couple more assumptions *)
lemma classes_between_unchanged_subset2:
 "\<lbrakk> classes_between P C C' \<inter> classes_changed P P' = {}; P \<turnstile> C \<preceq>\<^sup>* C'; P' \<turnstile> C' \<preceq>\<^sup>* Object \<rbrakk>
  \<Longrightarrow> classes_between P' C C' \<subseteq> classes_between P C C'"
apply (frule classes_unchanged_set)
apply clarify
apply (cut_tac b = x and P = "\<lambda>x. P' \<turnstile> x \<preceq>\<^sup>* C' \<longrightarrow> P \<turnstile> C \<preceq>\<^sup>* x \<and> P \<turnstile> x \<preceq>\<^sup>* C'" in rtrancl_induct, simp+)
 apply clarify
 apply (erule impE, fastforce)
 apply (metis (no_types, hide_lams) rtrancl.rtrancl_into_rtrancl rtrancl.rtrancl_refl 
   same_class_same_superclass subcls1_confluent subcls_of_Obj_acyclic)
apply simp
done

lemma classes_between_unchanged_subcls2:
 "\<lbrakk> classes_between P C C' \<inter> classes_changed P P' = {};
    P \<turnstile> C \<preceq>\<^sup>* C'; P' \<turnstile> C' \<preceq>\<^sup>* Object;
    P' \<turnstile> C \<preceq>\<^sup>* C''; P' \<turnstile> C'' \<preceq>\<^sup>* C' \<rbrakk>
   \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* C''"
apply (drule classes_between_unchanged_subset2, simp+)
apply blast
done

lemma classes_between_unchanged_subcls3:
 "\<lbrakk> classes_between P C C' \<inter> classes_changed P P' = {};
    P \<turnstile> C \<preceq>\<^sup>* C'; P' \<turnstile> C' \<preceq>\<^sup>* Object;
    P' \<turnstile> C \<preceq>\<^sup>* C''; P' \<turnstile> C'' \<preceq>\<^sup>* C' \<rbrakk>
   \<Longrightarrow> P \<turnstile> C'' \<preceq>\<^sup>* C'"
apply (drule classes_between_unchanged_subset2, simp+)
apply blast
done

lemma classes_between_unchanged_same_set:
 "\<lbrakk> classes_between P C C' \<inter> classes_changed P P' = {};
    P \<turnstile> C \<preceq>\<^sup>* C'; P' \<turnstile> C' \<preceq>\<^sup>* Object \<rbrakk>
  \<Longrightarrow> classes_between P C C' = classes_between P' C C'"
apply rule
 apply (rule classes_between_unchanged_subset, simp)
apply (rule classes_between_unchanged_subset2, simp+)
done

lemma classes_between_classes_changed_sym:
 "\<lbrakk> classes_between P C C' \<inter> classes_changed P P' = {};
    P \<turnstile> C \<preceq>\<^sup>* C'; P' \<turnstile> C' \<preceq>\<^sup>* Object \<rbrakk>
 \<Longrightarrow> classes_between P' C C' \<inter> classes_changed P' P = {}"
apply (frule classes_between_unchanged_same_set, simp+)
apply (cut_tac P = P and P' = P' in classes_changed_sym)
apply simp
done

(*****************************Methods*********************************)


(* HERE: is this an unnecessary special case of previous lemma? *)
lemma classes_unchanged_sees_methods_exists:
 "\<lbrakk> classes_between P C C' \<inter> classes_changed P P' = {}; P \<turnstile> C \<preceq>\<^sup>* C'; P' \<turnstile> C' \<preceq>\<^sup>* Object;
     \<exists>D' fs ms. class P' Object = \<lfloor>(D', fs, ms)\<rfloor>;
     P \<turnstile> C sees_methods Mm \<rbrakk>
 \<Longrightarrow> \<exists>Mm. P' \<turnstile> C sees_methods Mm"
apply (rule subcls_Obj_sees_methods_exists)
apply (frule classes_between_unchanged_subcls, simp+)
done


lemma classes_between_do_not_see_methods:
 "\<lbrakk> P \<turnstile> C sees_methods Mm; Mm M = Some(m,C'); D \<noteq> C'; D \<in> classes_between P C C' \<rbrakk>
  \<Longrightarrow> \<exists>D' fs ms. class P D = Some(D',fs,ms) \<and> map_of ms M = None"
apply clarsimp
apply (cut_tac Pa = "\<lambda>C Mm. Mm M = \<lfloor>(m, C')\<rfloor> \<longrightarrow> P \<turnstile> C \<preceq>\<^sup>* D
    \<longrightarrow> (\<exists>D' fs ms. class P D = \<lfloor>(D', fs, ms)\<rfloor> \<and> map_of ms M = None)"
  in Methods.induct, simp)
  apply clarify
 apply clarify
 apply (case_tac "Ca = D") apply simp
 apply (erule disjE, clarsimp)
  apply (subgoal_tac "P \<turnstile> D \<preceq>\<^sup>* Object")
   prefer 2
   apply (drule sees_methods_sub_Obj)
   apply (rule subcls_of_Obj, simp+)
  apply (drule subcls_of_Obj_acyclic, force, simp)
 apply simp
 apply (erule impE)
  apply (drule_tac C = Ca in subcls1I, simp)
  apply (simp add: subcls1_confluent)
 apply simp
apply simp
done

(* Important! *)
lemma classes_unchanged_sees_method_same:
 "\<lbrakk> classes_between P C C' \<inter> classes_changed P P' = {}; P \<turnstile> C sees_methods Mm;
     P' \<turnstile> C sees_methods Mm'; Mm M = Some(m,C') \<rbrakk>
  \<Longrightarrow> Mm' M = Some(m,C')"
apply (frule sees_methods_decl_above, simp)
apply (frule classes_between_unchanged_subcls, simp)
apply (cut_tac a = C and b = C' and
  P = "\<lambda>C''. \<forall>Mm Mm'. P \<turnstile> C \<preceq>\<^sup>* C'' \<longrightarrow> P \<turnstile> C'' sees_methods Mm \<longrightarrow>
           P' \<turnstile> C'' sees_methods Mm' \<longrightarrow>
           Mm M = \<lfloor>(m, C')\<rfloor> \<longrightarrow> Mm' M = \<lfloor>(m, C')\<rfloor>" in converse_rtrancl_induct, simp)
  apply clarsimp
  apply (drule_tac Mm = Mma in visible_methods_exist, simp, clarsimp)
  apply (drule classes_between_unchanged, simp+)
  apply (rule_tac ?a2.0 = Mm'a in Methods.cases, simp+)
 apply clarsimp
 apply (drule_tac D = y in classes_between_do_not_see_methods, simp)
   apply (metis (no_types, lifting) r_into_rtrancl sees_methods_sub_Obj subcls1D subcls_of_Obj_acyclic subcls_self_superclass)
  apply simp
 apply (drule_tac C'' = y in classes_between_unchanged, simp+)
 apply (frule subcls1D, clarsimp)
 apply (erule impE) apply auto[1]
 apply (rule_tac ?a2.0 = Mma in Methods.cases, simp+)
 apply (rule_tac ?a2.0 = Mm'a in Methods.cases, simp+)
 apply (erule_tac x = Mmaa in allE, erule impE, simp)
 apply (erule_tac x = Mmb in allE, erule impE, simp)
 apply (erule impE) apply auto[1]
 apply (simp add: map_add_Some_iff)
apply simp
done

lemma classes_unchanged_sees_same_method:
 "\<lbrakk> classes_between P C C' \<inter> classes_changed P P' = {};
     P' \<turnstile> C' \<preceq>\<^sup>* Object; \<exists>D' fs ms. class P' Object = \<lfloor>(D', fs, ms)\<rfloor>;
     P \<turnstile> C sees M,b: Ts\<rightarrow>T = m in C' \<rbrakk>
  \<Longrightarrow> P' \<turnstile> C sees M,b: Ts\<rightarrow>T = m in C'"
apply (frule sees_method_decl_above)
apply (clarsimp simp add: Method_def)
apply (frule classes_unchanged_sees_methods_exists, simp+)
apply (clarify, rule_tac x = Mma in exI, simp)
apply (rule classes_unchanged_sees_method_same, simp+)
done


lemma classes_unchanged_sees_same_method2:
 "\<lbrakk> classes_between P C C' \<inter> classes_changed P P' = {};
     P \<turnstile> C \<preceq>\<^sup>* C'; P \<turnstile> C' \<preceq>\<^sup>* Object; \<exists>D' fs ms. class P Object = \<lfloor>(D', fs, ms)\<rfloor>;
     P' \<turnstile> C sees M,b: Ts\<rightarrow>T = m in C' \<rbrakk>
  \<Longrightarrow> P \<turnstile> C sees M,b: Ts\<rightarrow>T = m in C'"
apply (frule sees_method_decl_above)
apply (drule classes_between_classes_changed_sym, simp+)
 apply (meson Method_def sees_methodsD subcls_of_Obj)
apply (rule classes_unchanged_sees_same_method, simp+)
done


(********************* Fields ************************)

(* HERE: is this an unnecessary special case of previous lemma? *)
lemma classes_unchanged_has_fields_exists:
 "\<lbrakk> classes_between P C C' \<inter> classes_changed P P' = {}; P \<turnstile> C \<preceq>\<^sup>* C'; P' \<turnstile> C' \<preceq>\<^sup>* Object;
     \<exists>D' fs ms. class P' Object = \<lfloor>(D', fs, ms)\<rfloor>;
     P \<turnstile> C has_fields FDTs \<rbrakk>
 \<Longrightarrow> \<exists>FDTs. P' \<turnstile> C has_fields FDTs"
apply (rule subcls_Obj_has_fields_exists)
apply (frule classes_between_unchanged_subcls, simp+)
done


lemma classes_between_do_not_see_fields:
 "\<lbrakk> P \<turnstile> C has_fields FDTs; map_of (map (\<lambda>((F,D),b,T). (F,(D,b,T))) FDTs) F = Some(C',b,T);
     D \<noteq> C'; D \<in> classes_between P C C' \<rbrakk>
  \<Longrightarrow> \<exists>D' fs ms. class P D = Some(D',fs,ms) \<and> map_of fs F = None"
apply clarsimp
apply (cut_tac
  Pa = "\<lambda>C FDTs. map_of (map (\<lambda>((F,D),b,T). (F,(D,b,T))) FDTs) F = Some(C',b,T) \<longrightarrow>
    P \<turnstile> C \<preceq>\<^sup>* D \<longrightarrow> (\<exists>D' fs ms. class P D = \<lfloor>(D', fs, ms)\<rfloor> \<and> map_of fs F = None)"
  in Fields.induct, simp)
   prefer 2 apply clarify
 apply (subgoal_tac "map_of (map ((\<lambda>((F, D), b, T). (F, D, b, T)) \<circ> (\<lambda>(F, y). ((F, Ca), y))) fs)
   = map_of (map (\<lambda>(F, y). (F, Ca, y)) fs)")
  prefer 2
  apply (simp add: map_of_remap_insertmap)
 apply clarsimp
 apply (case_tac "Ca = D", clarsimp)
  apply (erule disjE)
   apply (drule map_of_insertmap_Some_eq, simp)
  apply (clarify, drule map_of_insertmap_NoneD, simp)
 apply (erule disjE)
  apply (drule map_of_insertmap_Some_eq)
  apply (subgoal_tac "P \<turnstile> D \<preceq>\<^sup>* Object")
   prefer 2
   apply (drule has_fields_sub_Obj)
   apply (rule subcls_of_Obj, simp+)
  apply (drule subcls_of_Obj_acyclic, force, simp)
 apply simp
 apply (erule impE)
  apply (drule_tac C = Ca in subcls1I, simp)
  apply (simp add: subcls1_confluent)
 apply simp
apply simp
done

(* Important! *)
lemma classes_unchanged_has_field_same:
 "\<lbrakk> classes_between P C C' \<inter> classes_changed P P' = {}; P \<turnstile> C has_fields FDTs;
     P' \<turnstile> C has_fields FDTs'; map_of (map (\<lambda>((F,D),b,T). (F,(D,b,T))) FDTs) F = Some(C',b,T) \<rbrakk>
  \<Longrightarrow> map_of (map (\<lambda>((F,D),b,T). (F,(D,b,T))) FDTs') F = Some(C',b,T)"
apply (frule_tac F = F and D = C' and b = b and T = T in has_fields_decl_above)
 apply (simp add: map_of_SomeD map_of_remap_SomeD2)
apply (frule classes_between_unchanged_subcls, simp)
apply (cut_tac a = C and b = C' and
  P = "\<lambda>C''. \<forall>FDTs FDTs'. P \<turnstile> C \<preceq>\<^sup>* C'' \<longrightarrow> P \<turnstile> C'' has_fields FDTs \<longrightarrow>
           P' \<turnstile> C'' has_fields FDTs' \<longrightarrow>
           map_of (map (\<lambda>((F,D),b,T). (F,(D,b,T))) FDTs) F = Some(C',b,T) \<longrightarrow>
           map_of (map (\<lambda>((F,D),b,T). (F,(D,b,T))) FDTs') F = Some(C',b,T)"
      in converse_rtrancl_induct, simp)
  apply clarsimp
  apply (drule_tac FDTs = FDTsa and F = F and D = C' and b = b and T = T
    in visible_fields_exist)
   apply (simp add: map_of_remap_SomeD2, clarsimp)
  apply (drule classes_between_unchanged, simp+)
  apply (rule_tac ?a2.0 = FDTs'a in Fields.cases, simp+)
    apply (clarsimp simp add: map_add_def, rule conjI)
     apply (metis map_of_insertmap_NoneD map_of_remap_insertmap option.distinct(1))
    apply (clarsimp simp add: map_of_remap_insertmap)
    apply (drule_tac D = C' in map_of_insertmap_SomeD2', fastforce)
   apply (clarsimp simp add: map_of_remap_insertmap)
   apply (drule_tac D = C' in map_of_insertmap_SomeD2', fastforce)
 apply clarsimp
 apply (drule_tac D = y in classes_between_do_not_see_fields, simp)
   apply (metis (no_types, lifting) has_fields_sub_Obj r_into_rtrancl subcls1D subcls_of_Obj_acyclic subcls_self_superclass)
  apply simp
 apply (drule_tac C'' = y in classes_between_unchanged, simp+)
 apply (frule subcls1D, clarsimp)
 apply (erule impE) apply auto[1]
 apply (rule_tac ?a2.0 = FDTsa in Fields.cases, simp+)
  apply (clarsimp simp add: map_of_remap_insertmap)
  apply (erule disjE)
   apply (drule_tac fs = fsa and D = Ca in map_of_insertmap_NoneD', fastforce)
  apply clarify
  apply (cut_tac P = P' and C = z in subcls_Obj_has_fields_exists)
    apply (meson has_fields_sub_Obj subcls1.subcls1I subcls1_confluent)
   using has_fieldsD apply blast
  apply (erule_tac x = FDTsa in allE, clarsimp, erule_tac x = FDTsb in allE, simp)
  apply (drule_tac P = P' and C = Ca in has_fields_rec, simp+)
  apply (drule has_fields_fun, simp, clarsimp)
  apply (clarsimp simp add: map_add_def, rule conjI)
   apply (metis map_of_remap_insertmap option.distinct(1))
  apply (clarsimp simp add: map_of_remap_insertmap)
 apply (drule_tac D = C' in map_of_insertmap_SomeD2', fastforce)
 apply (clarsimp simp add: map_of_remap_insertmap)
done


lemma classes_unchanged_sees_same_field:
 "\<lbrakk> classes_between P C C' \<inter> classes_changed P P' = {};
    P' \<turnstile> C' \<preceq>\<^sup>* Object; \<exists>D' fs ms. class P' Object = \<lfloor>(D', fs, ms)\<rfloor>;
    P \<turnstile> C sees F,b:t in C' \<rbrakk>
   \<Longrightarrow> P' \<turnstile> C sees F,b:t in C'"
apply (frule sees_field_decl_above)
apply (clarsimp simp add: sees_field_def)
apply (frule classes_unchanged_has_fields_exists, simp+)
apply (clarify, rule_tac x = FDTsa in exI, simp)
apply (rule classes_unchanged_has_field_same, simp+)
done


lemma classes_unchanged_sees_same_field2:
 "\<lbrakk> classes_between P C C' \<inter> classes_changed P P' = {};
     P \<turnstile> C \<preceq>\<^sup>* C'; P \<turnstile> C' \<preceq>\<^sup>* Object; \<exists>D' fs ms. class P Object = \<lfloor>(D', fs, ms)\<rfloor>;
    P' \<turnstile> C sees F,b:t in C' \<rbrakk>
   \<Longrightarrow> P \<turnstile> C sees F,b:t in C'"
apply (frule sees_field_decl_above)
apply (drule classes_between_classes_changed_sym, simp+)
 apply (meson has_fieldsD sees_field_def subcls_of_Obj)
apply (rule classes_unchanged_sees_same_field, simp+)
done


(***********************************
(* overrides *)


lemma classes_unchanged_closest_above_same:
 "\<lbrakk> classes_between P C' D \<inter> classes_changed P P' = {};
    P \<turnstile> C sees M,b:Ts \<rightarrow> T = m in D; P \<turnstile> C' \<preceq>\<^sup>* C;
    P \<turnstile> C' \<preceq>\<^sup>* C''; P' \<turnstile> D \<preceq>\<^sup>* Object; \<exists>D' fs ms. class P' Object = \<lfloor>(D', fs, ms)\<rfloor>;
    P \<turnstile> C'' closestAbove C' that (\<lambda>P C''. \<exists>m' D'. P \<turnstile> C'' sees M,b :  Ts\<rightarrow>T = m' in D') \<rbrakk>
 \<Longrightarrow>
    P' \<turnstile> C'' closestAbove C' that (\<lambda>P C''. \<exists>m' D'. P \<turnstile> C'' sees M,b :  Ts\<rightarrow>T = m' in D')"
apply (clarsimp simp add: Closest_above_that_def)

apply (subgoal_tac "P \<turnstile> C'' \<preceq>\<^sup>* C")
 prefer 2
 apply (erule_tac x = C in allE, erule impE, simp, blast)
 apply simp

apply (subgoal_tac "P \<turnstile> C'' \<preceq>\<^sup>* D")
 prefer 2
 apply (rule_tac y = C in rtrancl_trans, simp)
 apply (rule sees_method_decl_above, simp)

apply (subgoal_tac "P' \<turnstile> C' \<preceq>\<^sup>* C''")
 prefer 2
 apply (rule_tac P = P in classes_between_unchanged_subcls)
  apply (rule subset_empty_intersect, simp)
  apply (rule classes_between_subset_below, simp)
  apply simp
 apply simp

apply (subgoal_tac "P \<turnstile> C'' \<preceq>\<^sup>* D'a")
 prefer 2
 apply (rule sees_method_decl_above, simp)

apply (subgoal_tac "P \<turnstile> D'a \<preceq>\<^sup>* D")
 prefer 2
 apply (rule sees_method_decl_mono, simp_all)

apply (subgoal_tac "classes_between P D'a D \<inter> classes_changed P P' = {}")
 prefer 2
 apply (rule subset_empty_intersect, simp)
 apply (rule classes_between_subset_between, simp+)

apply (subgoal_tac "P' \<turnstile> D'a \<preceq>\<^sup>* D")
 prefer 2
 apply (rule_tac P = P in classes_between_unchanged_subcls, simp+)

apply (subgoal_tac "P' \<turnstile> D'a \<preceq>\<^sup>* Object")
 prefer 2
 apply (rule rtrancl_trans, simp+)

apply (subgoal_tac "classes_between P C'' D'a \<inter> classes_changed P P' = {}")
 prefer 2
 apply (rule subset_empty_intersect, simp)
 apply (rule classes_between_subset_between, simp+)

apply (subgoal_tac "P' \<turnstile> C'' sees M :  Ts\<rightarrow>T = m' in D'a, static b")
 prefer 2
 apply (rule_tac P = P in classes_unchanged_sees_same_method, simp+)

apply (subgoal_tac "classes_between P C' C'' \<inter> classes_changed P P' = {}")
 prefer 2
 apply (rule subset_empty_intersect, simp)
 apply (rule classes_between_subset_below, simp+)

apply (subgoal_tac "P' \<turnstile> C'' \<preceq>\<^sup>* D")
 prefer 2
 apply (rule_tac P = P in classes_between_unchanged_subcls)
  apply (rule subset_empty_intersect, simp)
  apply (rule classes_between_subset_above, simp)
  apply simp
 apply simp

apply (subgoal_tac "P' \<turnstile> C'' \<preceq>\<^sup>* Object")
 prefer 2
 apply (rule rtrancl_trans, simp+)

apply (subgoal_tac "\<forall>C''a. P' \<turnstile> C' \<preceq>\<^sup>* C''a \<and>
  (\<exists>m' D'. P' \<turnstile> C''a sees M :  Ts\<rightarrow>T = m' in D', static b) \<longrightarrow> P' \<turnstile> C'' \<preceq>\<^sup>* C''a")
 prefer 2
 apply clarsimp
 apply (frule_tac P = P' and C' = C'' and C'' = C''a in subcls_confluent, assumption, erule disjE)
  apply simp

 apply (subgoal_tac "P \<turnstile> C' \<preceq>\<^sup>* C''a")
  prefer 2
  apply (rule_tac C' = C'' in classes_between_unchanged_subcls2, simp+)

 apply (subgoal_tac "P' \<turnstile> D'b \<preceq>\<^sup>* D'a")
  prefer 2
  apply (rule_tac P = P' and C = C'' and C' = C''a in sees_method_decl_mono, simp+)

 apply (subgoal_tac "P' \<turnstile> D'b \<preceq>\<^sup>* D")
  prefer 2
  apply (rule_tac y = D'a in rtrancl_trans, simp+)

 apply (subgoal_tac "P' \<turnstile> C''a \<preceq>\<^sup>* D'b")
  prefer 2
  apply (rule sees_method_decl_above, simp)

 apply (subgoal_tac "P' \<turnstile> C' \<preceq>\<^sup>* D'b")
  prefer 2
  apply (rule_tac y = C''a in rtrancl_trans, simp+)

 apply (subgoal_tac "P \<turnstile> C' \<preceq>\<^sup>* D'b")
  prefer 2
  apply (rule classes_between_unchanged_subcls2, simp+)

 apply (subgoal_tac "P \<turnstile> D'b \<preceq>\<^sup>* D")
  prefer 2
  apply (rule classes_between_unchanged_subcls3, simp+)

 apply (subgoal_tac "classes_between P C' D'b \<inter> classes_changed P P' = {}")
  prefer 2
  apply (rule subset_empty_intersect, simp)
  apply (rule classes_between_subset_below, simp+)

 apply (subgoal_tac "P \<turnstile> C''a \<preceq>\<^sup>* D'b")
  prefer 2
  apply (rule classes_between_unchanged_subcls3, simp+)

 apply (subgoal_tac "classes_between P C''a D'b \<inter> classes_changed P P' = {}")
  prefer 2
  apply (rule_tac R = "classes_between P C' D'b" in subset_empty_intersect, simp)
  apply (rule classes_between_subset_above, simp+)

 apply (subgoal_tac "P \<turnstile> D'b \<preceq>\<^sup>* Object")
  prefer 2
  apply (meson rtrancl_trans sees_method_sub_Obj subcls_of_Obj)

 apply (subgoal_tac "\<exists>D' fs ms. class P Object = \<lfloor>(D', fs, ms)\<rfloor>")
  prefer 2
  apply (rule sees_method_Object_exists, simp)

 apply (subgoal_tac "P \<turnstile> C''a sees M :  Ts\<rightarrow>T = m'a in D'b, static b")
  prefer 2
  apply (rule_tac P' = P' in classes_unchanged_sees_same_method2, simp+)

 apply (subgoal_tac "P \<turnstile> C''a \<preceq>\<^sup>* C''")
  prefer 2
  apply (rule classes_between_unchanged_subcls3, simp+)

 apply (erule_tac x = C''a in allE)
 apply (erule impE, simp, blast)
 apply (subgoal_tac "C'' = C''a")
  prefer 2
  apply (meson sees_method_sub_Obj subcls_of_Obj_acyclic)
 apply simp
apply blast
done


lemma classes_unchanged_overrides_same:
 "\<lbrakk> classes_between P C' D \<inter> classes_changed P P' = {};
    P' \<turnstile> D \<preceq>\<^sup>* Object; \<exists>D' fs ms. class P' Object = \<lfloor>(D', fs, ms)\<rfloor>;
    P \<turnstile> C', m', D' overrides C, M = m in D : Ts \<rightarrow> T, static b \<rbrakk>
 \<Longrightarrow> P' \<turnstile> C', m', D' overrides C, M = m in D : Ts \<rightarrow> T, static b"
apply (frule overrides_subcls)
apply (clarsimp simp add: Overrides_def)

apply (subgoal_tac "P' \<turnstile> C sees M :  Ts\<rightarrow>T = m in D, static b")
 prefer 2
 apply (rule classes_unchanged_sees_same_method, simp_all)
   apply (frule subset_empty_intersect, rule_tac C' = C in classes_between_subset_above)
   apply (simp, rule sees_method_decl_above, simp+)

apply (subgoal_tac "P \<turnstile> C' \<preceq>\<^sup>* C''")
 prefer 2
 apply (rule closest_above_subcls, simp)

apply (subgoal_tac "classes_between P C'' C \<inter> classes_changed P P' = {}")
 prefer 2
 apply (rule subset_empty_intersect, simp)
  apply (rule classes_between_subset_between, simp+)
 apply (rule sees_method_decl_above, simp)

apply (subgoal_tac "P' \<turnstile> C'' \<preceq>\<^sup>* C")
 prefer 2
 apply (rule_tac P = P in classes_between_unchanged_subcls, simp+)

apply (subgoal_tac "P \<turnstile> C'' \<preceq>\<^sup>* D'")
 prefer 2
 apply (rule sees_method_decl_above, simp)

apply (subgoal_tac "P \<turnstile> D' \<preceq>\<^sup>* D")
 prefer 2
 apply (rule_tac C' = C'' in sees_method_decl_mono, simp+)

apply (subgoal_tac "classes_between P C'' D' \<inter> classes_changed P P' = {}")
 prefer 2
 apply (rule subset_empty_intersect, simp)
  apply (rule classes_between_subset_between, simp+)

apply (subgoal_tac "classes_between P D' D \<inter> classes_changed P P' = {}")
 prefer 2
 apply (rule subset_empty_intersect, simp)
  apply (rule classes_between_subset_above, simp+)

apply (subgoal_tac "P' \<turnstile> D' \<preceq>\<^sup>* D")
 prefer 2
 apply (rule_tac P = P in classes_between_unchanged_subcls, simp+)

apply (subgoal_tac "P' \<turnstile> D' \<preceq>\<^sup>* Object")
 prefer 2
 apply (rule rtrancl_trans, simp+)

apply (subgoal_tac "P' \<turnstile> C'' sees M :  Ts\<rightarrow>T = m' in D', static b")
 prefer 2
 apply (rule_tac P = P in classes_unchanged_sees_same_method, simp+)

apply (subgoal_tac "P' \<turnstile> C'' closestAbove C' that (\<lambda>P C''. \<exists>m' D'. P \<turnstile> C'' sees M :  Ts\<rightarrow>T = m' in D', static b)")
 prefer 2
 apply (rule classes_unchanged_closest_above_same, simp+)

apply blast
done

***********************************************)

(* HERE: move this when done *)
(* not currently used *)
lemma cyclic_implies:
 "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* C'; P \<turnstile> C' \<preceq>\<^sup>* C; C \<noteq> C' \<rbrakk>
\<Longrightarrow> \<forall>x. P \<turnstile> C \<preceq>\<^sup>* x \<longrightarrow> P \<turnstile> x \<preceq>\<^sup>* C"
apply clarify
apply (frule_tac b = x and P = "\<lambda>x. P \<turnstile> C \<preceq>\<^sup>* x \<longrightarrow> P \<turnstile> x \<preceq>\<^sup>* C'" in rtrancl_induct, simp)
 apply clarsimp
 apply (case_tac "y = C'")
  apply (metis rtrancl_trans subcls1_confluent)
 apply (simp add: subcls1_confluent)
apply simp
done

(* HERE: below is currently unused, but may need it in the future *)
(*
(* is this true? trying to find a way to obtain the new acyclicity assumption using simpler
  assumptions *)
lemma
 "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* Object \<longrightarrow> P' \<turnstile> C \<preceq>\<^sup>* Object (*;
    P' cyclicAbove C' \<longrightarrow> P cyclicAbove C' *) \<rbrakk>
\<Longrightarrow> (* NO - not enough *)
   \<forall>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<and> P' \<turnstile> C \<preceq>\<^sup>* C' \<and> P' \<turnstile> C' \<preceq>\<^sup>* C \<longrightarrow> P \<turnstile> C' \<preceq>\<^sup>* C"
apply clarsimp
apply (case_tac "C = C'", simp)
apply (case_tac "P \<turnstile> C \<preceq>\<^sup>* Object")
 apply simp
 apply (drule subcls_of_Obj_acyclic, simp)+
 apply simp
apply simp
thm subcls_of_Obj_acyclic subcls_of_Obj_acyclic1
find_theorems name:acyclic
oops
*)

(* this direction requires an acyclicity assumption *)
(* we were attempting to modify the assumption used, but for now we'll stick with what we have below *)
(*
lemma classes_between_unchanged_subset2:
 "\<lbrakk> classes_between P C C' \<inter> classes_changed P P' = {}; P \<turnstile> C \<preceq>\<^sup>* C';
(*    \<forall>C''. P \<turnstile> C' \<preceq>\<^sup>* C'' \<and> P' \<turnstile> C' \<preceq>\<^sup>* C'' \<and> P' \<turnstile> C'' \<preceq>\<^sup>* C' \<longrightarrow> P \<turnstile> C'' \<preceq>\<^sup>* C' (* i.e., acyclicity has not been introduced *)*)
    P' cyclicAbove C' \<longrightarrow> P cyclicAbove C' \<rbrakk>
  \<Longrightarrow> classes_between P' C C' \<subseteq> classes_between P C C'"
apply (frule classes_unchanged_set)
apply clarify
apply (cut_tac b = x and P = "\<lambda>x. P' \<turnstile> C \<preceq>\<^sup>* x \<and> P' \<turnstile> x \<preceq>\<^sup>* C' \<longrightarrow> P \<turnstile> C \<preceq>\<^sup>* x \<and> P \<turnstile> x \<preceq>\<^sup>* C'" in rtrancl_induct, simp+)
 apply clarify
 apply (erule impE, fastforce)
(* apply (subgoal_tac "P \<turnstile> y \<prec>\<^sup>1 z")
  prefer 2
  apply (metis (no_types, lifting) same_class_same_superclass) *)
 (****)
 defer
 apply (metis (no_types, lifting) cyclic_above_def rtrancl.rtrancl_into_rtrancl subcls1_confluent subcls_confluent
apply simp
oops
(**)
apply (case_tac "P' cyclicAbove C'", simp)
 apply (clarsimp simp add: cyclic_above_def) defer
apply simp
apply (subgoal_tac "P \<turnstile> y \<prec>\<^sup>1 z")
 prefer 2
 apply (metis (no_types, lifting) same_class_same_superclass)
done
*)

end