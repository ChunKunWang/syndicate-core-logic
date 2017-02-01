Add LoadPath "/home/amos/applpi".

Require Import libapplpi.
Require Import SG_applpi_string.

(** Result channel **)
Axiom result_chan : chan unit false.
Definition succ : proc := OutAtom result_chan tt.

(** Catch IO exception **)
Axiom IOexn_chan : chan unit false.
Definition IOexn := OutAtom IOexn_chan tt.

(** Catch a system failure **)
Axiom system_failure_chan : chan unit false.
Definition failure := OutAtom system_failure_chan tt.

Definition may_fail := nuP
  (fun x => parP (InAtom x)
    (parP (OutAtom x tt) (x ?? (fun _ => OutAtom system_failure_chan tt)))).

Record Manifest : Set := manifest
  { volume_id : String; 
    coordinator_id : String;
    owner_id : String;
    file_id : String;
    file_version : String;
    size : String}.






