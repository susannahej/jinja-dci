(*  Title:      Jinja/Common/ClassesChanged.thy
    Author:    Susannah Mansky, UIUC 2016
*)

(* HERE: write a better .thy description *)
section {* Theory around the classes changed from one program to another, and how
  if classes are not changed, the same things are visible in those classes *}

theory ClassesChanged
imports "../MapOfThy" "../SupplSetThy" Exceptions
begin

(***)

(* a class is considered changed if it exists only in one program or the other,
  or exists in both but is different *)
definition classes_changed :: "'m prog \<Rightarrow> 'm prog \<Rightarrow> cname set" where
"classes_changed P1 P2
   = foldl (\<lambda>a (cn, c). if class P1 cn \<noteq> class P2 cn then insert cn a else a) {} (P1@P2)"
(*"classes_changed P1 P2 = {cn. class P1 cn \<noteq> class P2 cn}"*)

lemma classes_changed_equiv:
 "cn \<in> classes_changed P1 P2
   = ((class P1 cn \<noteq> class P2 cn) \<and> (\<exists>x. fst x = cn \<and> x \<in> set (P1@P2)))"
apply (simp only: classes_changed_def class_def)
apply (cut_tac f = "fst" and y = "(cn, the (map_of P2 cn))" and s = "{}" and
  ?l2.0 = "P1@P2" and P = "\<lambda>x. map_of P1 x \<noteq> map_of P2 x" in foldl_if_insert)
apply (subgoal_tac "\<forall>l s. (foldl (\<lambda>a (cn, c). if map_of P1 cn \<noteq> map_of P2 cn then insert cn a else a) s l =
foldl (\<lambda>a x. if map_of P1 (fst x) \<noteq> map_of P2 (fst x) then insert (fst x) a else a) s l)")
 prefer 2
 apply (clarify, rule list.induct, simp)
 apply (meson foldl_cong prod.case_eq_if)
apply (erule_tac x = "P1@P2" in allE, erule_tac x = "{}" in allE, clarsimp)
done

lemma classes_changed_exists:
  "cn \<in> classes_changed P1 P2 \<Longrightarrow> class P1 cn \<noteq> None \<or> class P2 cn \<noteq> None"
apply (simp only: classes_changed_equiv, erule conjE)
apply (simp only: class_exists_equiv2)
done


definition class_changed :: "'m prog \<Rightarrow> 'm prog \<Rightarrow> cname \<Rightarrow> bool" where
"class_changed P1 P2 cn = (class P1 cn \<noteq> class P2 cn)"

lemma class_changed_exists:
  "class_changed P1 P2 cn \<Longrightarrow> class P1 cn \<noteq> None \<or> class P2 cn \<noteq> None"
apply (simp add: class_changed_def)
apply (rule classical)
apply (subgoal_tac "class P1 cn = None \<and> class P2 cn = None")
 prefer 2
 apply force
apply simp
done

lemma classes_changed_class_changed[simp]: "cn \<in> classes_changed P1 P2 = class_changed P1 P2 cn"
apply (simp add: classes_changed_equiv)
apply (rule iffI)
 apply (simp add: class_changed_def)
apply (frule class_changed_exists)
apply (simp add: class_changed_def class_def)
apply (meson map_of_SomeD)
done

lemma classes_changed_self[simp]: "classes_changed P P = {}"
 by (auto simp add: class_changed_def)

lemma classes_changed_sym: "classes_changed P P' = classes_changed P' P"
 by (auto simp add: class_changed_def)

lemma class_changed_equiv:
 "class_changed P1 P2 cn =
   ((class P1 cn \<noteq> class P2 cn) \<and> (class P1 cn \<noteq> None \<or> class P2 cn \<noteq> None))"
apply (simp only: classes_changed_class_changed [THEN sym] classes_changed_equiv class_exists_equiv2)
done


(* lemma relating classes_changed to execution changes, or lack thereof *)
lemma classes_changed_nin_same: "\<lbrakk> cn \<notin> classes_changed P P'\<rbrakk> \<Longrightarrow> class P cn = class P' cn"
apply (clarsimp simp add: class_changed_equiv)
by (metis option.exhaust prod_cases3)

lemma classes_unchanged_set: "\<lbrakk> S \<inter> classes_changed P P' = {} \<rbrakk>
  \<Longrightarrow> \<forall>C \<in> S. class P C = class P' C"
apply (clarsimp simp add: disjoint_iff_not_equal)
apply (rule classes_changed_nin_same, force)
done

(** Program structure lemmas **)

lemma class_changed_singleton:
 "class_changed [t] P' (fst t) \<Longrightarrow> class_changed (t # P) P' (fst t)"
 by (simp add: class_changed_def class_def)

lemma class_changed_singleton2:
 "class_changed P [t] (fst t) \<Longrightarrow> class_changed P (t # P') (fst t)"
 by (simp add: class_changed_def class_def)

lemma not_class_changed_singleton:
 "\<not> class_changed [t] P' (fst t) \<Longrightarrow> fst t \<notin> classes_changed (t # P) P'"
apply simp
apply (rule classical, simp)
apply (erule notE, simp add: class_changed_def class_def)
done

(* HERE: might want to change next few lemmas slightly; they work as is for now *)
lemma classes_changed_cons_changed_subset:
 "class_changed [t] P' (fst t) \<Longrightarrow> classes_changed P P' \<subseteq> classes_changed (t # P) P'"
by (smt class_changed_singleton class_cons classes_changed_class_changed classes_changed_equiv
  classes_changed_nin_same subsetI)

lemma classes_unchanged_cons_changed_subset:
"\<not> class_changed [t] P' (fst t) \<Longrightarrow> classes_changed P P' - {fst t} \<subseteq> classes_changed (t # P) P'"
by (smt DiffE class_cons classes_changed_equiv classes_changed_nin_same insertCI subsetI)

lemma classes_unchanged_cons_changed_subset2:
 "\<not> class_changed [t] P' (fst t) \<Longrightarrow> classes_changed (t # P) P' \<subseteq> classes_changed P P'"
apply (frule_tac P = P in not_class_changed_singleton)
apply (metis class_cons classes_changed_equiv classes_changed_nin_same subsetI)
done

lemma classes_changed_cons:
 "classes_changed (t # P) P' = (classes_changed P P' - {fst t})
                     \<union> (if class_changed [t] P' (fst t) then {fst t} else {})"
apply (case_tac "class_changed [t] P' (fst t)")
 apply simp
 apply rule
  apply (metis class_cons classes_changed_equiv classes_changed_nin_same insertCI subsetI)
 apply (rule insert_subsetI)
  apply (drule class_changed_singleton, simp)
  apply (rule classes_changed_cons_changed_subset, simp)
apply simp
apply rule
 apply (rule not_in_Diff_subsetI)
  apply (rule classes_unchanged_cons_changed_subset2, simp)
  apply (cut_tac not_class_changed_singleton, simp+)
apply (rule classes_unchanged_cons_changed_subset, simp)
done


lemma class_changed_same_cons:
 "fst t \<notin> classes_changed (t#P) (t#P')"
 by (simp add: class_changed_def class_def)

lemma classes_changed_same_cons:
 "classes_changed (t # P) (t # P') = classes_changed P P' - {fst t}"
proof(cases "fst t \<in> classes_changed P P'")
  case True
  then show ?thesis using class_changed_same_cons[where t=t and P=P and P'=P']
    classes_changed_cons[where t=t] by (auto simp: class_changed_def class_cons)
next
  case False
  then show ?thesis using class_changed_same_cons[where t=t and P=P and P'=P']
    by (auto simp: class_changed_def) (metis (no_types, lifting) class_cons)+
qed

lemma classes_changed_int_Cons:
assumes "coll \<inter> classes_changed P P' = {}"
shows "coll \<inter> classes_changed (t # P) (t # P') = {}"
proof(cases "fst t \<in> classes_changed P P'")
  case True
  then have "classes_changed P P' = classes_changed (t # P) (t # P') \<union> {fst t}"
    using classes_changed_same_cons[where t=t and P=P and P'=P'] by fastforce
  then show ?thesis using assms by simp
next
  case False
  then have "classes_changed P P' = classes_changed (t # P) (t # P')"
    using classes_changed_same_cons[where t=t and P=P and P'=P'] by fastforce
  then show ?thesis using assms by simp
qed

end