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


Fixpoint FS_Create (file_name : string) (file_st : list (string * list bool)) : option (list (string * list bool)) :=
  match file_st with
    | nil => Some [(file_name,nil)]
    | hd::tl => match hd with
                  | (name,content) => if string_dec file_name name then None
                                      else match FS_Create file_name tl with
                                             | None => None
                                             | Some a => Some (hd::a) 
                                           end
                end 
  end.

Definition FS_Create_Main (file_name : string) (file_st : FileSystemState) : option FileSystemState :=
  match file_st with
    | file_sys_st st => match FS_Create file_name st with
                          | None => None
                          | Some new => Some (file_sys_st new)
                        end
  end.

Fixpoint FS_Delete (file_name : string) (file_st : list (string * list bool)) : option (list (string * list bool)) :=
  match file_st with
    | nil => None
    | hd::tl => match hd with
                  | (name, content) => if string_dec file_name name then Some tl
                                       else match FS_Delete file_name tl with
                                              | None => None
                                              | Some a => Some (hd::a)
                                            end
                end
  end.

Definition FS_Delete_Main (file_name : string) (file_st : FileSystemState) : option FileSystemState :=
  match file_st with
    | file_sys_st st => match FS_Create file_name st with
                          | None => None
                          | Some new => Some (file_sys_st new)
                        end
  end.

Fixpoint FS_Rename (old_file_name : string) (new_file_name : string) (file_st : list (string * list bool)) : option (list (string * list bool)) :=
  match file_st with
    | nil => None
    | hd::tl => match hd with
                  | (name, content) => if string_dec new_file_name name then None
                                       else if string_dec old_file_name name then match FS_Rename old_file_name new_file_name tl with
                                                                                    | None => None
                                                                                    | Some a => Some ((new_file_name, content)::a)
                                                                                   end
                                       else match FS_Rename old_file_name new_file_name tl with
                                              | None => None
                                              | Some a => Some (hd::a)
                                            end
                end                     
  end.

Definition FS_Rename_Main (old_file_name : string) (new_file_name : string) (file_st : FileSystemState) : option FileSystemState :=
  match file_st with
    | file_sys_st st => match FS_Rename old_file_name new_file_name st with
                          | None => None
                          | Some new => Some (file_sys_st new)
                        end
  end.

Fixpoint Truncate_Length (new_len : nat) (content : list bool) : option (list bool) :=
  match new_len with 
    | O => Some []
    | S rest => match content with
                  | [] => None
                  | hd::tl => match Truncate_Length rest tl with
                                | None => None
                                | Some new_content => Some (hd::new_content)
                              end
                end
  end.

Fixpoint FS_Truncate (file_name : string) (new_len : nat) (file_st : list (string * list bool)) : option (list (string * list bool)) :=
  match file_st with
    | [] => None
    | hd::tl => match hd with
                  | (name, content) => if string_dec file_name name then match Truncate_Length new_len content with
                                                                           | None => None
                                                                           | Some new_content => Some ((name, new_content)::tl)
                                                                         end
                                       else match FS_Truncate file_name new_len tl with
                                              | None => None
                                              | Some a => Some (hd::a)
                                             end
                 end
  end.

Definition FS_Truncate_Main (file_name : string) (new_len : nat) (file_st : FileSystemState) : option FileSystemState :=
  match file_st with
    | file_sys_st st => match FS_Truncate file_name new_len st with
                          | None => None
                          | Some new => Some (file_sys_st new)
                        end
  end.


Fixpoint Visit_FS (file_st : list (string * list bool)) : list string :=
  match file_st with
    | [] => []
    | hd::tl => match hd with
                  | (name, content) => (name::Visit_FS tl)
                end
  end.

Definition Return_All_Filename (file_st : FileSystemState) : list string :=
  match file_st with
    | file_sys_st st => Visit_FS st
  end.

Lemma Check_Write_Doesnot_Change_Filename : forall file_st file_name offset content, match FS_Write_Main file_name offset content file_st with 
                                                               | None => True
                                                               | Some new_st => Return_All_Filename new_st = Return_All_Filename file_st
                                                              end.
intros.
destruct file_st.
simpl.
induction fs_st0.
simpl.
auto.
simpl.
destruct a.
destruct (string_dec file_name s).
destruct (write_content l offset content).
simpl.
reflexivity.
auto.
destruct (FS_Write file_name offset content fs_st0).
simpl.
simpl in IHfs_st0.
rewrite IHfs_st0.
reflexivity.
auto.
Qed.

Fixpoint Visit_FS_Append (file_list : list string) (filename : string) : list string :=
  match file_list with
    | [] => [filename]
    | hd::tl => hd::Visit_FS_Append tl filename
  end.

Lemma Check_Create_Append: forall file_st file_name, match FS_Create_Main file_name file_st with
                                                       | None => True
                                                       | Some new_st => Visit_FS_Append (Return_All_Filename file_st) file_name = Return_All_Filename new_st
                                                     end.
intros.
destruct file_st.
simpl.
induction fs_st0.
simpl.
reflexivity.
simpl.
destruct a.
destruct (string_dec file_name s).
auto.
destruct (FS_Create file_name fs_st0).
simpl.
simpl in IHfs_st0.
rewrite IHfs_st0.
reflexivity.
auto.
Qed.

Fixpoint Check_OUF_2 (file_name : string) (file_st : list (string * list bool)) : Prop :=
  match file_st with
    | [] => True
    | hd::tl => match hd with
                  | (name, content) => ~(file_name = name) /\ Check_OUF_2 file_name tl
                end
  end.

Fixpoint Check_OUF (file_st : list (string * list bool)) : Prop :=
  match file_st with
    | [] => True
    | hd::tl => match hd with
                  | (name, content) => Check_OUF_2 name tl /\ Check_OUF tl
                end
  end.

Definition Only_Unique_Filename (file_st : FileSystemState) : Prop :=
  match file_st with
    | file_sys_st st => Check_OUF st
  end.

Fixpoint Check_OUF_2_Allfilename (file_name : string) (file_st : list string) : Prop :=
  match file_st with
    | [] => True
    | hd::tl => ~(file_name = hd) /\ Check_OUF_2_Allfilename file_name tl
  end.

Fixpoint Check_OUF_Allfilename (file_st : list string) : Prop :=
  match file_st with
    | [] => True
    | hd::tl => Check_OUF_2_Allfilename hd tl /\ Check_OUF_Allfilename tl
  end.

Definition Return_Filename_Unique (file_st : FileSystemState) : Prop :=
  Check_OUF_Allfilename (Return_All_Filename file_st).

Lemma Check_Write : forall file_st file_name offset content, Return_Filename_Unique file_st -> match FS_Write_Main file_name offset content file_st with 
                                                                                               | None => True
                                                                                               | Some a => Return_Filename_Unique a
                                                                                             end.
intros.
destruct file_st.
simpl.
pose Check_Write_Doesnot_Change_Filename.
specialize y.
specialize (y (file_sys_st fs_st0) file_name offset content).
simpl in y.
destruct (FS_Write file_name offset content fs_st0).
simpl in y.
unfold Return_Filename_Unique.
unfold Return_All_Filename.
unfold Return_Filename_Unique in H.
unfold Return_All_Filename in H.
rewrite y.
auto.
auto.
Qed.


