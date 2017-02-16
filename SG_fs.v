Add LoadPath "/home/amos/applpi".

Require Import libapplpi.
Require Import SG_applpi_string.
Require Import Coq.FSets.FMapList.

Record FileSystemState : Set := file_sys_st
  {fs_st : list (String * list bool)}.

Inductive empty_set : Set := .

Definition FS_Read (file_name : String) (offset : nat) (file_st : FileSystemState) : bool :=
  match file_name with
    | _ => match offset with
             | O => false
             | s => true
           end
  end.
