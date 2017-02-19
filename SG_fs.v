Add LoadPath "/home/amos/applpi".

Require Import libapplpi.
Require Import SG_applpi_string.
Require Import Coq.FSets.FMapList.
Require Import Coq.Strings.String.
Import ListNotations.

Record FileSystemState : Set := file_sys_st
  {fs_st : list (string * list bool)}.

(* Helper func: search offset and return content for FS_Read *)
Fixpoint return_offset (content : list bool) (offset : nat) : option bool :=
  match offset with
    | O => match content with (* offset == 0 *)
             | [] => None
             | a :: t => Some a
           end
    | S rest => match content with (* offset != 0 and keeping searching *)
                  | [] => None
                  | a :: t => return_offset t rest
                 end 
  end.

(* Helper func: search file_name in fs and return content of the offset *)
Fixpoint FS_Read (file_name : string) (offset : nat) (file_st : list (string * list bool)) : option bool :=
  match file_st with
    | nil => None
    | a::t => match a with (* compare the file_name and keeping searching from fs *)
             | (s,b) => if string_dec file_name s then return_offset b offset
                        else FS_Read file_name offset t
           end
  end.

(** FS_Read_Main using FS_Read and return_offset *)
Definition FS_Read_Main (file_name : string) (offset : nat) (file_st : FileSystemState) : option bool :=
  match file_st with
    | file_sys_st a => FS_Read file_name offset a
  end.

(* Helper func: search offset and write new content *)
Fixpoint write_content (content : list bool) (offset : nat) (new_content : bool) : option (list bool) :=
  match offset with
    | O => match content with
             | [] => Some [new_content]
             | a :: t => Some (new_content :: t) (* write the new content and the rest appends *)
           end
    | S rest => match content with
                  | [] => None (* if the file doesn't have enough sapce, do nothing *)
                  | a :: t => write_content t rest new_content
                 end 
  end.

(* Helper func: search file_name and offset; then, write the content *)
Fixpoint FS_Write (file_name : string) (offset : nat) (content : bool) (file_st : list (string * list bool)) : option (list (string * list bool)) :=
  match file_st with
    | nil => None
    | a::t => match a with
             | (s,b) => if string_dec file_name s then match write_content b offset content with
                                                         | None => None
                                                         | Some a => Some ((s,a)::t)
                                                        end
                        else match FS_Write file_name offset content t with
                               | None => None
                               | Some b => Some (a::b)
                             end
              end
  end.

(** FS_Write_Main using FS_Write and write_content *)
Definition FS_Write_Main (file_name : string) (offset : nat) (content : bool) (file_st : FileSystemState) : option FileSystemState :=
  match file_st with
    | file_sys_st a => match FS_Write file_name offset content a with
                         | None => None
                         | Some new => Some (file_sys_st new)
                       end
  end.


Definition FS_Create (file_name : string) (file_st : FileSystemState) : option FileSystemState :=
  match file_name with
    | file_sys_st st => 
  end.



