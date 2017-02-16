Add LoadPath "/home/amos/applpi".

Require Import libapplpi.
Require Import SG_applpi_string.
Require Import Coq.FSets.FMapList.

Record FileSystemState : Set := file_sys_st
  {fs_st : list (String * list bool)}.

(*Definition Read (file_name : String) (offset : nat) (file_st : FileSystemState) : bool :=. *)