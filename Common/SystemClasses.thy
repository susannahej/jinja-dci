(*  Title:      HOL/MicroJava/J/SystemClasses.thy

    Author:     Gerwin Klein
    Copyright   2002 Technische Universitaet Muenchen
    
    Added more Exception types - Susannah Mansky
    2017, UIUC
*)

section {* System Classes *}

theory SystemClasses
imports Decl Exceptions
begin

text {*
  This theory provides definitions for the @{text Object} class,
  and the system exceptions.
*}

definition ObjectC :: "'m cdecl"
where
  "ObjectC \<equiv> (Object, (undefined,[],[]))"

definition NullPointerC :: "'m cdecl"
where
  "NullPointerC \<equiv> (NullPointer, (Object,[],[]))"

definition ClassCastC :: "'m cdecl"
where
  "ClassCastC \<equiv> (ClassCast, (Object,[],[]))"

definition OutOfMemoryC :: "'m cdecl"
where
  "OutOfMemoryC \<equiv> (OutOfMemory, (Object,[],[]))"

definition NoClassDefFoundC :: "'m cdecl"
where
  "NoClassDefFoundC \<equiv> (NoClassDefFoundError, (Object,[],[]))"

definition IncompatibleClassChangeC :: "'m cdecl"
where
  "IncompatibleClassChangeC \<equiv> (IncompatibleClassChangeError, (Object,[],[]))"

definition NoSuchFieldC :: "'m cdecl"
where
  "NoSuchFieldC \<equiv> (NoSuchFieldError, (Object,[],[]))"

definition NoSuchMethodC :: "'m cdecl"
where
  "NoSuchMethodC \<equiv> (NoSuchMethodError, (Object,[],[]))"

definition SystemClasses :: "'m cdecl list"
where
  "SystemClasses \<equiv> [ObjectC, NullPointerC, ClassCastC, OutOfMemoryC, NoClassDefFoundC,
  IncompatibleClassChangeC, NoSuchFieldC, NoSuchMethodC]"

end
