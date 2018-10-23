(*  Title:      Jinja/JVM/JVMState.thy

    Original Author:     Cornelia Pusch, Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
    Expanded to include features for statics and dynamic class initialization by Susannah Mansky
    2016-17, UIUC
*)

chapter {* Jinja Virtual Machine \label{cha:jvm} *}

section {* State of the JVM *}

theory JVMState imports "../Common/Objects" begin


type_synonym 
  pc = nat

definition start_sheap :: "'m prog \<Rightarrow> sheap"
where
  "start_sheap P = (\<lambda>x. None)"

definition start_sheap_preloaded :: "'m prog \<Rightarrow> sheap"
where
  "start_sheap_preloaded P \<equiv> fold (\<lambda>(C,cl) f. f(C := Some (sblank P C, Prepared))) P (\<lambda>x. None)"

subsection {* Frame Stack *}

datatype init_call_status = No_ics | Calling cname | ICalling cname
                          | Called | Throwing addr
	\<comment> \<open>No_ics = not currently calling or waiting for the result of an initialization procedure call\<close>
  \<comment> \<open>Calling C = current instruction is calling for initialization of C\<close>
  \<comment> \<open>ICalling C = initialization procedure is calling for initialization of C
        due to the initialization of one of its subclasses (in this frame)\<close>
  \<comment> \<open>Called = current instruction called initialization and is waiting for the result\<close>
  \<comment> \<open>Throwing a = frame threw or was thrown an error causing erroneous end of initialization
        procedure\<close>

type_synonym
  frame = "val list \<times> val list \<times> cname \<times> mname \<times> pc \<times> init_call_status"
  \<comment> \<open>operand stack\<close> 
  \<comment> \<open>registers (including this pointer, method parameters, and local variables)\<close>
  \<comment> \<open>name of class where current method is defined\<close>
  \<comment> \<open>current method\<close>
  \<comment> \<open>program counter within frame\<close>
  \<comment> \<open>indicates initialization call frame status\<close>

translations
  (type) "frame" <= (type) "val list \<times> val list \<times> char list \<times> char list \<times> nat \<times> init_call_status"

fun curr_stk :: "frame \<Rightarrow> val list" where
"curr_stk (stk, loc, C, M, pc, ics) = stk"

fun curr_class :: "frame \<Rightarrow> cname" where
"curr_class (stk, loc, C, M, pc, ics) = C"

fun curr_method :: "frame \<Rightarrow> mname" where
"curr_method (stk, loc, C, M, pc, ics) = M"

fun curr_pc :: "frame \<Rightarrow> nat" where
"curr_pc (stk, loc, C, M, pc, ics) = pc"

fun init_status :: "frame \<Rightarrow> init_call_status" where
 "init_status (stk, loc, C, M, pc, ics) = ics"

fun ics_of :: "frame \<Rightarrow> init_call_status" where
 "ics_of fr = snd(snd(snd(snd(snd fr))))"

subsection {* Runtime State *}

type_synonym
  jvm_state = "addr option \<times> heap \<times> frame list \<times> sheap"  
  \<comment> \<open>exception flag, heap, frames, information about statics\<close>

translations
  (type) "jvm_state" <= (type) "nat option \<times> heap \<times> frame list \<times> sheap"

fun frames_of :: "jvm_state \<Rightarrow> frame list" where
"frames_of (xp, h, frs, sh) = frs"

abbreviation sheap :: "jvm_state \<Rightarrow> sheap" where
"sheap js \<equiv> snd (snd (snd js))"

end
