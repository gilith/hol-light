(* ========================================================================= *)
(* MEMORY SAFETY FOR THE H INTERFACE                                         *)
(* Joe Leslie-Hurd and Rebekah Leslie-Hurd                                   *)
(*                                                                           *)
(* A formalization of Rebekah Leslie's PhD thesis:                           *)
(*   http://leslier.com/thesis.pdf                                           *)
(*                                                                           *)
(* Complete:                                                                 *)
(*                                                                           *)
(* 1. A model of the machine state relevant to operating system memory       *)
(*    safety, including a notion of wellformed states.                       *)
(*                                                                           *)
(* 2. A definition of the 4 domains relevant to the memory-safe H interface  *)
(*    for low-level memory operations in a Haskell operating system:         *)
(*      E: Haskell environment                                               *)
(*      H: H interface                                                       *)
(*      K: Operating system kernel                                           *)
(*      U: User processes                                                    *)
(*                                                                           *)
(* 3. A model of the actions that domains can perform, defined in terms of   *)
(*    their effect on wellformed states.                                     *)
(*                                                                           *)
(* 4. A definition of operating system memory safety as a noninterference    *)
(*    policy between the domains.                                            *)
(*                                                                           *)
(* In progress:                                                              *)
(*                                                                           *)
(* 1. A definition of the view of the machine state for each domain.         *)
(*                                                                           *)
(* 2. A refinement of the actions that are deterministic with respect to the *)
(*    domain views.                                                          *)
(*                                                                           *)
(* 3. A proof that the refined actions satisfy Rushby's unwinding conditions *)
(*    for the system noninterference policy.                                 *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Theory requirements.                                                      *)
(* ------------------------------------------------------------------------- *)

import_theories
  ["base";
   "natural-bits";
   "byte";
   "word10";
   "word12"];;

needs "opentheory/theories/tools.ml";;
needs "opentheory/theories/word10/word10-tools.ml";;

(* ------------------------------------------------------------------------- *)
(* Theory interpretation.                                                    *)
(* ------------------------------------------------------------------------- *)

export_interpretation "opentheory/theories/h/h.int";;

(* ------------------------------------------------------------------------- *)
(* Definition of memory safety for the H interface.                          *)
(* ------------------------------------------------------------------------- *)

export_theory "h-def";;

(* ~~~~~~~~~~~~~~ *)
(* Region lengths *)
(* ~~~~~~~~~~~~~~ *)

let region_length_tybij =
  define_newtype ("l","region_length") ("n",`:num`);;

export_thm region_length_tybij;;

(* ~~~~~~~~~~~~~~~ *)
(* Address offsets *)
(* ~~~~~~~~~~~~~~~ *)

(* Superpage offsets *)

let superpage_offset_tybij =
  define_newtype ("si","superpage_offset") ("w",`:word10`);;

export_thm superpage_offset_tybij;;

let num_to_superpage_offset_def = new_definition
  `!n.
     num_to_superpage_offset n =
     mk_superpage_offset (num_to_word10 n)`;;

export_thm num_to_superpage_offset_def;;

let superpage_offset_add_def = new_definition
  `!si n.
     superpage_offset_add si n =
     mk_superpage_offset
       (word10_add (dest_superpage_offset si) (num_to_word10 n))`;;

export_thm superpage_offset_add_def;;

(* Page offsets *)

let page_offset_tybij =
  define_newtype ("i","page_offset") ("w",`:word12`);;

export_thm page_offset_tybij;;

(* ~~~~~~~~~~~~~~~~~~ *)
(* Physical addresses *)
(* ~~~~~~~~~~~~~~~~~~ *)

(* Physical superpage addresses *)

let physical_superpage_address_tybij =
  define_newtype ("psa","physical_superpage_address") ("w",`:word10`);;

export_thm physical_superpage_address_tybij;;

let num_to_physical_superpage_address_def = new_definition
  `!n.
     num_to_physical_superpage_address n =
     mk_physical_superpage_address (num_to_word10 n)`;;

export_thm num_to_physical_superpage_address_def;;

let physical_superpage_address_add_def = new_definition
  `!psa n.
     physical_superpage_address_add psa n =
     mk_physical_superpage_address
       (word10_add (dest_physical_superpage_address psa) (num_to_word10 n))`;;

export_thm physical_superpage_address_add_def;;

(* Physical page addresses *)

let physical_page_address_tybij =
  define_newtype ("ppa","physical_page_address")
    ("r", `:physical_superpage_address # superpage_offset`);;

export_thm physical_page_address_tybij;;

let physical_page_address_suc_def = new_definition
  `!ppa.
     physical_page_address_suc ppa =
     let (psa,si) = dest_physical_page_address ppa in
     let si' = superpage_offset_add si 1 in
     let psa' =
         if si' = num_to_superpage_offset 0 then
           physical_superpage_address_add psa 1
         else
           psa in
     mk_physical_page_address (psa',si')`;;

export_thm physical_page_address_suc_def;;

let physical_page_address_add_def = new_recursive_definition num_RECURSION
  `(!ppa. physical_page_address_add ppa 0 = ppa) /\
   (!ppa n.
      physical_page_address_add ppa (SUC n) =
      physical_page_address_add (physical_page_address_suc ppa) n)`;;

export_thm physical_page_address_add_def;;

(* Physical addresses *)

let physical_address_tybij =
  define_newtype ("pa","physical_address")
    ("r", `:physical_page_address # page_offset`);;

export_thm physical_address_tybij;;

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Regions of physical memory *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let (physical_region_induct,physical_region_recursion) =
  let (induct,recursion) = define_type
    "physical_region =
       PhysicalRegion
         physical_page_address
         region_length" in
  let induct' = prove
    (`!p.
        (!s l. p (PhysicalRegion s l)) ==>
        !pr. p pr`,
     ACCEPT_TAC induct)
  and recursion' = prove
    (`!f.
        ?(fn : physical_region -> A).
          (!s l. fn (PhysicalRegion s l) = f s l)`,
     MATCH_ACCEPT_TAC recursion) in
  (induct',recursion');;

export_thm physical_region_induct;;
export_thm physical_region_recursion;;

let physical_region_start_def =
  new_recursive_definition physical_region_recursion
  `!s l. physical_region_start (PhysicalRegion s l) = s`;;

export_thm physical_region_start_def;;

let physical_region_length_def =
  new_recursive_definition physical_region_recursion
  `!s l. physical_region_length (PhysicalRegion s l) = l`;;

export_thm physical_region_length_def;;

let physical_region_to_list_def =
  new_recursive_definition physical_region_recursion
  `!s l.
     physical_region_to_list (PhysicalRegion s l) =
     MAP (physical_page_address_add s) (interval 0 (dest_region_length l))`;;

export_thm physical_region_to_list_def;;

let forall_physical_region_def = new_definition
  `!p pr.
     forall_physical_region p pr <=>
     ALL p (physical_region_to_list pr)`;;

export_thm forall_physical_region_def;;

let exists_physical_region_def = new_definition
  `!p pr.
     exists_physical_region p pr <=>
     EX p (physical_region_to_list pr)`;;

export_thm exists_physical_region_def;;

let member_physical_region_def = new_definition
  `!ppa pr.
     member_physical_region ppa pr <=>
     MEM ppa (physical_region_to_list pr)`;;

export_thm member_physical_region_def;;

let is_physical_subregion_def = new_definition
  `!pr1 pr2.
     is_physical_subregion pr1 pr2 <=>
     forall_physical_region (\ppa. member_physical_region ppa pr2) pr1`;;

export_thm is_physical_subregion_def;;

(* ~~~~~~~~~~~~~~~~~ *)
(* Virtual addresses *)
(* ~~~~~~~~~~~~~~~~~ *)

(* Virtual superpage addresses *)

let virtual_superpage_address_tybij =
  define_newtype ("vsa","virtual_superpage_address") ("w",`:word10`);;

export_thm virtual_superpage_address_tybij;;

let num_to_virtual_superpage_address_def = new_definition
  `!n.
     num_to_virtual_superpage_address n =
     mk_virtual_superpage_address (num_to_word10 n)`;;

export_thm num_to_virtual_superpage_address_def;;

let virtual_superpage_address_add_def = new_definition
  `!vsa n.
     virtual_superpage_address_add vsa n =
     mk_virtual_superpage_address
       (word10_add (dest_virtual_superpage_address vsa) (num_to_word10 n))`;;

export_thm virtual_superpage_address_add_def;;

(* Virtual page addresses *)

let virtual_page_address_tybij =
  define_newtype ("vpa","virtual_page_address")
    ("r", `:virtual_superpage_address # superpage_offset`);;

export_thm virtual_page_address_tybij;;

let virtual_page_address_suc_def = new_definition
  `!vpa.
     virtual_page_address_suc vpa =
     let (vsa,si) = dest_virtual_page_address vpa in
     let si' = superpage_offset_add si 1 in
     let vsa' =
         if si' = num_to_superpage_offset 0 then
           virtual_superpage_address_add vsa 1
         else
           vsa in
     mk_virtual_page_address (vsa',si')`;;

export_thm virtual_page_address_suc_def;;

let virtual_page_address_add_def = new_recursive_definition num_RECURSION
    `(!vpa. virtual_page_address_add vpa 0 = vpa) /\
     (!vpa n.
        virtual_page_address_add vpa (SUC n) =
        virtual_page_address_add (virtual_page_address_suc vpa) n)`;;

export_thm virtual_page_address_add_def;;

(* Virtual addresses *)

let virtual_address_tybij =
  define_newtype ("va","virtual_address")
    ("r", `:virtual_page_address # page_offset`);;

export_thm virtual_address_tybij;;

(* ~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Regions of virtual memory *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let (virtual_region_induct,virtual_region_recursion) =
  let (induct,recursion) = define_type
    "virtual_region =
       VirtualRegion
         virtual_page_address
         region_length" in
  let induct' = prove
    (`!p.
        (!s l. p (VirtualRegion s l)) ==>
        !pr. p pr`,
     ACCEPT_TAC induct)
  and recursion' = prove
    (`!f.
        ?(fn : virtual_region -> A).
          (!s l. fn (VirtualRegion s l) = f s l)`,
     MATCH_ACCEPT_TAC recursion) in
  (induct',recursion');;

export_thm virtual_region_induct;;
export_thm virtual_region_recursion;;

let virtual_region_start_def =
  new_recursive_definition virtual_region_recursion
  `!s l. virtual_region_start (VirtualRegion s l) = s`;;

export_thm virtual_region_start_def;;

let virtual_region_length_def =
  new_recursive_definition virtual_region_recursion
  `!s l. virtual_region_length (VirtualRegion s l) = l`;;

export_thm virtual_region_length_def;;

let virtual_region_to_list_def =
  new_recursive_definition virtual_region_recursion
  `!s l.
     virtual_region_to_list (VirtualRegion s l) =
     MAP (virtual_page_address_add s) (interval 0 (dest_region_length l))`;;

export_thm virtual_region_to_list_def;;

let forall_virtual_region_def = new_definition
  `!p vr.
     forall_virtual_region p vr <=>
     ALL p (virtual_region_to_list vr)`;;

export_thm forall_virtual_region_def;;

let exists_virtual_region_def = new_definition
  `!p vr.
     exists_virtual_region p vr <=>
     EX p (virtual_region_to_list vr)`;;

export_thm exists_virtual_region_def;;

let member_virtual_region_def = new_definition
  `!ppa vr.
     member_virtual_region ppa vr <=>
     MEM ppa (virtual_region_to_list vr)`;;

export_thm member_virtual_region_def;;

let is_virtual_subregion_def = new_definition
  `!vr1 vr2.
     is_virtual_subregion vr1 vr2 <=>
     forall_virtual_region (\ppa. member_virtual_region ppa vr2) vr1`;;

export_thm is_virtual_subregion_def;;

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* User and kernel virtual addresses *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let is_kernel_superpage_address_def = new_definition
  `!vsa.
     is_kernel_superpage_address vsa <=>
     let w = dest_virtual_superpage_address vsa in
     word10_bit w 9 /\ word10_bit w 8`;;

export_thm is_kernel_superpage_address_def;;

let is_user_superpage_address_def = new_definition
  `!vsa.
     is_user_superpage_address vsa <=>
     ~is_kernel_superpage_address vsa`;;

export_thm is_user_superpage_address_def;;

let is_kernel_page_address_def = new_definition
  `!vpa.
     is_kernel_page_address vpa <=>
     let (vsa,si) = dest_virtual_page_address vpa in
     is_kernel_superpage_address vsa`;;

export_thm is_kernel_page_address_def;;

let is_user_page_address_def = new_definition
  `!vpa.
     is_user_page_address vpa <=>
     ~is_kernel_page_address vpa`;;

export_thm is_user_page_address_def;;

let is_kernel_address_def = new_definition
  `!va.
     is_kernel_address va <=>
     let (vpa,i) = dest_virtual_address va in
     is_kernel_page_address vpa`;;

export_thm is_kernel_address_def;;

let is_user_address_def = new_definition
  `!va.
     is_user_address va <=>
     ~is_kernel_address va`;;

export_thm is_user_address_def;;

let is_user_region_def = new_definition
  `!vr.
     is_user_region vr <=>
     forall_virtual_region is_user_page_address vr`;;

export_thm is_user_region_def;;

let is_kernel_region_def = new_definition
  `!vr.
     is_kernel_region vr <=>
     forall_virtual_region is_kernel_page_address vr`;;

export_thm is_kernel_region_def;;

(* ~~~~~~~~~ *)
(* Page data *)
(* ~~~~~~~~~ *)

let page_data_tybij =
  define_newtype ("d","page_data")
    ("f", `:page_offset -> byte`);;

export_thm page_data_tybij;;

let zero_page_data_def = new_definition
  `zero_page_data = mk_page_data (\i. num_to_byte 0)`;;

export_thm zero_page_data_def;;

let update_page_data_def = new_definition
  `!k v d.
      update_page_data k v d =
      mk_page_data (\i. if i = k then v else dest_page_data d i)`;;

export_thm update_page_data_def;;

(* ~~~~~~~~~~~ *)
(* Page tables *)
(* ~~~~~~~~~~~ *)

(* Page table addresses *)

new_type_abbrev("page_table",`:physical_page_address`);;

(* Page table data *)

new_type_abbrev("page_table_index",`:superpage_offset`);;

let page_table_data_tybij =
  define_newtype ("t","page_table_data")
    ("f", `:page_table_index -> physical_page_address option`);;

export_thm page_table_data_tybij;;

(* ~~~~~~~~~~~~~~~~ *)
(* Page directories *)
(* ~~~~~~~~~~~~~~~~ *)

(* Page directory addresses *)

new_type_abbrev("page_directory",`:physical_page_address`);;

(* Page directory entries *)

let (page_directory_entry_induct,
     page_directory_entry_recursion) = define_type
    "page_directory_entry =
       Superpage physical_superpage_address
     | Table page_table";;

export_thm page_directory_entry_induct;;
export_thm page_directory_entry_recursion;;

let case_page_directory_entry_def =
  new_recursive_definition page_directory_entry_recursion
  `(!f g psa. case_page_directory_entry f g (Superpage psa) = (f psa : A)) /\
   (!f g pt. case_page_directory_entry f g (Table pt) = (g pt : A))`;;

export_thm case_page_directory_entry_def;;

(* Page directory data *)

new_type_abbrev("page_directory_index",`:virtual_superpage_address`);;

let page_directory_data_tybij =
  define_newtype ("d","page_directory_data")
    ("f", `:page_directory_index -> page_directory_entry option`);;

export_thm page_directory_data_tybij;;

(* ~~~~~~~~~~ *)
(* Page types *)
(* ~~~~~~~~~~ *)

let (page_induct,page_recursion) = define_type
    "page =
       Environment page_data
     | Normal page_data
     | PageDirectory page_directory_data
     | PageTable page_table_data
     | NotInstalled";;

export_thm page_induct;;
export_thm page_recursion;;

let dest_environment_def = new_recursive_definition page_recursion
  `(!d. dest_environment (Environment d) = SOME d) /\
   (!d. dest_environment (Normal d) = NONE) /\
   (!pdd. dest_environment (PageDirectory pdd) = NONE) /\
   (!ptd. dest_environment (PageTable ptd) = NONE) /\
   (dest_environment NotInstalled = NONE)`;;

export_thm dest_environment_def;;

let dest_normal_def = new_recursive_definition page_recursion
  `(!d. dest_normal (Environment d) = NONE) /\
   (!d. dest_normal (Normal d) = SOME d) /\
   (!pdd. dest_normal (PageDirectory pdd) = NONE) /\
   (!ptd. dest_normal (PageTable ptd) = NONE) /\
   (dest_normal NotInstalled = NONE)`;;

export_thm dest_normal_def;;

let dest_environment_or_normal_def = new_recursive_definition page_recursion
  `(!d. dest_environment_or_normal (Environment d) = SOME d) /\
   (!d. dest_environment_or_normal (Normal d) = SOME d) /\
   (!pdd. dest_environment_or_normal (PageDirectory pdd) = NONE) /\
   (!ptd. dest_environment_or_normal (PageTable ptd) = NONE) /\
   (dest_environment_or_normal NotInstalled = NONE)`;;

export_thm dest_environment_or_normal_def;;

let dest_page_directory_def = new_recursive_definition page_recursion
  `(!d. dest_page_directory (Environment d) = NONE) /\
   (!d. dest_page_directory (Normal d) = NONE) /\
   (!pdd. dest_page_directory (PageDirectory pdd) = SOME pdd) /\
   (!ptd. dest_page_directory (PageTable ptd) = NONE) /\
   (dest_page_directory NotInstalled = NONE)`;;

export_thm dest_page_directory_def;;

let dest_page_table_def = new_recursive_definition page_recursion
  `(!d. dest_page_table (Environment d) = NONE) /\
   (!d. dest_page_table (Normal d) = NONE) /\
   (!pdd. dest_page_table (PageDirectory pdd) = NONE) /\
   (!ptd. dest_page_table (PageTable ptd) = SOME ptd) /\
   (dest_page_table NotInstalled = NONE)`;;

export_thm dest_page_table_def;;

let is_not_installed_def = new_recursive_definition page_recursion
  `(!d. is_not_installed (Environment d) = F) /\
   (!d. is_not_installed (Normal d) = F) /\
   (!pdd. is_not_installed (PageDirectory pdd) = F) /\
   (!ptd. is_not_installed (PageTable ptd) = F) /\
   (is_not_installed NotInstalled = T)`;;

export_thm is_not_installed_def;;

let is_environment_def = new_definition
  `!p. is_environment p <=> is_some (dest_environment p)`;;

export_thm is_environment_def;;

let is_normal_def = new_definition
  `!p. is_normal p <=> is_some (dest_normal p)`;;

export_thm is_normal_def;;

let is_page_directory_def = new_definition
  `!p. is_page_directory p <=> is_some (dest_page_directory p)`;;

export_thm is_page_directory_def;;

let is_page_table_def = new_definition
  `!p. is_page_table p <=> is_some (dest_page_table p)`;;

export_thm is_page_table_def;;

let is_page_directory_or_table_def = new_definition
  `!p.
     is_page_directory_or_table p <=>
     is_page_directory p \/ is_page_table p`;;

export_thm is_page_directory_or_table_def;;

let is_installed_def = new_definition
  `!p. is_installed p <=> ~is_not_installed p`;;

export_thm is_installed_def;;

(* ~~~~~~~~~~~~~~~~~~~~~~~ *)
(* The state of the system *)
(* ~~~~~~~~~~~~~~~~~~~~~~~ *)

(* Derived physical regions state *)

let (region_state_induct,region_state_recursion) = define_type
    "region_state =
       RegionState
         (physical_region set)
         (physical_region set)";;

export_thm region_state_induct;;
export_thm region_state_recursion;;

let initial_regions_def = new_recursive_definition region_state_recursion
  `!i a. initial_regions (RegionState i a) = i`;;

export_thm initial_regions_def;;

let all_regions_def = new_recursive_definition region_state_recursion
  `!i a. all_regions (RegionState i a) = a`;;

export_thm all_regions_def;;

(* A type of system states *)

let (state_induct,state_recursion) = define_type
    "state =
       State
         page_directory
         page_directory
         (physical_page_address -> page)
         region_state";;

export_thm state_induct;;
export_thm state_recursion;;

let cr3_def = new_recursive_definition state_recursion
  `!c r s g. cr3 (State c r s g) = c`;;

export_thm cr3_def;;

let reference_def = new_recursive_definition state_recursion
  `!c r s g. reference (State c r s g) = r`;;

export_thm reference_def;;

let status_def = new_recursive_definition state_recursion
  `!c r s g. status (State c r s g) = s`;;

export_thm status_def;;

let regions_def = new_recursive_definition state_recursion
  `!c r s g. regions (State c r s g) = g`;;

export_thm regions_def;;

let is_environment_page_def = new_definition
  `!s ppa. is_environment_page s ppa <=> is_environment (status s ppa)`;;

export_thm is_environment_page_def;;

let is_normal_page_def = new_definition
  `!s ppa. is_normal_page s ppa <=> is_normal (status s ppa)`;;

export_thm is_normal_page_def;;

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Virtual to physical mappings *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let translate_page_def = new_definition
  `!s pd vpa.
     translate_page s pd vpa =
     let (vsa,si) = dest_virtual_page_address vpa in
     case_option
       NONE
       (\pdd.
          case_option
            NONE
            (\pde.
               case_page_directory_entry
                 (\psa. SOME (mk_physical_page_address (psa,si)))
                 (\pt.
                    case_option
                      NONE
                      (\ptd. dest_page_table_data ptd si)
                      (dest_page_table (status s pt)))
                 pde)
            (dest_page_directory_data pdd vsa))
       (dest_page_directory (status s pd))`;;

export_thm translate_page_def;;

let translation_def = new_definition
  `!s va.
     translation s va =
     let (vpa,i) = dest_virtual_address va in
     case_option
       NONE
       (\ppa. SOME (mk_physical_address (ppa,i)))
       (translate_page s (cr3 s) vpa)`;;

export_thm translation_def;;

let table_mapped_in_directory_def = new_definition
  `!s pd pt.
     table_mapped_in_directory s pd pt <=>
     case_option
       F
       (\pdd. ?pdi. dest_page_directory_data pdd pdi = SOME (Table pt))
       (dest_page_directory (status s pd))`;;

export_thm table_mapped_in_directory_def;;

let mapped_page_def = new_definition
  `!s pd vpa.
     mapped_page s pd vpa <=>
     is_some (translate_page s pd vpa)`;;

export_thm mapped_page_def;;

let unmapped_page_def = new_definition
  `!s ppa.
     unmapped_page s ppa <=>
     !pd.
       is_page_directory (status s pd) ==>
       !vpa. ~(translate_page s pd vpa = SOME ppa)`;;

export_thm unmapped_page_def;;

let unmapped_normal_page_def = new_definition
  `!s ppa.
     unmapped_normal_page s ppa <=>
     unmapped_page s ppa /\ is_normal_page s ppa`;;

export_thm unmapped_normal_page_def;;

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Well-formed machine states *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let cr3_is_page_directory_def = new_definition
  `!s.
     cr3_is_page_directory s <=>
     is_page_directory (status s (cr3 s))`;;

export_thm cr3_is_page_directory_def;;

let reference_is_page_directory_def = new_definition
  `!s.
     reference_is_page_directory s <=>
     is_page_directory (status s (reference s))`;;

export_thm reference_is_page_directory_def;;

let reference_maps_kernel_addresses_def = new_definition
  `!s.
     reference_maps_kernel_addresses s <=>
     !vpa.
       mapped_page s (reference s) vpa ==>
       is_kernel_page_address vpa`;;

export_thm reference_maps_kernel_addresses_def;;

let reference_contains_environment_def = new_definition
  `!s.
     reference_contains_environment s <=>
     !ppa.
       is_environment (status s ppa) ==>
       ?vpa. translate_page s (reference s) vpa = SOME ppa`;;

export_thm reference_contains_environment_def;;

let environment_only_in_reference_def = new_definition
  `!s.
     environment_only_in_reference s <=>
     !pd vpa.
       case_option
         T
         (\ppa.
            is_environment (status s ppa) ==>
            mapped_page s (reference s) vpa)
         (translate_page s pd vpa)`;;

export_thm environment_only_in_reference_def;;

let page_directories_contain_reference_def = new_definition
  `!s.
     page_directories_contain_reference s <=>
     !pd vpa.
       is_page_directory (status s pd) /\
       is_kernel_page_address vpa ==>
       translate_page s pd vpa = translate_page s (reference s) vpa`;;

export_thm page_directories_contain_reference_def;;

let mapped_pages_are_available_def = new_definition
  `!s.
     mapped_pages_are_available s <=>
     !pd vpa.
        case_option
          T
          (\ppa. is_installed (status s ppa))
          (translate_page s pd vpa)`;;

export_thm mapped_pages_are_available_def;;

let table_pointers_are_page_tables_def = new_definition
  `!s.
     table_pointers_are_page_tables s <=>
     !pd pdi.
       case_option
         T
         (\pdd.
            case_option
              T
              (\pde.
                 case_page_directory_entry
                   (\spa. T)
                   (\ppa. is_page_table (status s ppa))
                   pde)
              (dest_page_directory_data pdd pdi))
         (dest_page_directory (status s pd))`;;

export_thm table_pointers_are_page_tables_def;;

let no_shared_page_tables_def = new_definition
  `!s.
     no_shared_page_tables s <=>
     !pt pd1 pd2 pdd1 pdd2 vsa1 vsa2.
       dest_page_directory (status s pd1) = SOME pdd1 /\
       dest_page_directory (status s pd2) = SOME pdd2 /\
       dest_page_directory_data pdd1 vsa1 = SOME (Table pt) /\
       dest_page_directory_data pdd2 vsa2 = SOME (Table pt) ==>
       vsa1 = vsa2 /\
       (is_kernel_superpage_address vsa1 \/ pd1 = pd2)`;;

export_thm no_shared_page_tables_def;;

let initial_regions_are_regions_def = new_definition
  `!s.
     initial_regions_are_regions s <=>
     initial_regions (regions s) SUBSET all_regions (regions s)`;;

export_thm initial_regions_are_regions_def;;

let regions_are_not_environment_def = new_definition
  `!s.
     regions_are_not_environment s <=>
     !r ppa.
       r IN all_regions (regions s) /\
       member_physical_region ppa r ==>
       ~is_environment (status s ppa)`;;

export_thm regions_are_not_environment_def;;

(* TODO *)
(* Need extra condition that all regions are subregions of initial regions? *)
(* Need extra condition that all regions are nonempty? *)

let wellformed_def = new_definition
  `!s.
     wellformed s <=>
     cr3_is_page_directory s /\
     page_directories_contain_reference s /\
     mapped_pages_are_available s /\
     table_pointers_are_page_tables s /\
     no_shared_page_tables s /\
     reference_is_page_directory s /\
     reference_maps_kernel_addresses s /\
     environment_only_in_reference s /\
     initial_regions_are_regions s /\
     regions_are_not_environment s`;;

export_thm wellformed_def;;

(* ~~~~~~~~~~~~~~~~ *)
(* Observable pages *)
(* ~~~~~~~~~~~~~~~~ *)

let observable_pages_tybij =
  define_newtype ("v","observable_pages")
    ("f", `:virtual_page_address ->
            (page_data # virtual_page_address set) option`);;

export_thm observable_pages_tybij;;

let translate_to_observable_pages_def = new_definition
  `!tr s.
     translate_to_observable_pages tr s =
     mk_observable_pages
       (\vpa.
          case_option
            NONE
            (\ppa.
               case_option
                 NONE
                 (\d. SOME (d, { vpa' | tr s vpa' = SOME ppa }))
                 (dest_environment_or_normal (status s ppa)))
            (tr s vpa))`;;

export_thm translate_to_observable_pages_def;;

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Protection domains and their view of the system state *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(* A type of protection domains *)

let (domain_induct,domain_recursion) =
  let (induct,recursion) = define_type
    "domain =
       EDomain
     | HDomain
     | KDomain
     | UDomain" in
  let induct' = prove
    (`!p.
        p EDomain /\
        p HDomain /\
        p KDomain /\
        p UDomain ==>
        !d. p d`,
     ACCEPT_TAC induct)
  and recursion' = prove
    (`!fe fh fk fu.
        ?(fn : domain -> A).
          fn EDomain = fe /\
          fn HDomain = fh /\
          fn KDomain = fk /\
          fn UDomain = fu`,
     MATCH_ACCEPT_TAC recursion) in
  (induct',recursion');;

export_thm domain_induct;;
export_thm domain_recursion;;

(* A type of domain view *)

new_type_abbrev("observable_pages_e",
  `:observable_pages`);;

new_type_abbrev("current_page_directory_h",
  `:page_directory`);;

new_type_abbrev("pages_h",
  `:physical_page_address -> page option`);;

new_type_abbrev("region_handles_h",
  `:region_state`);;

new_type_abbrev("reference_page_directory_h",
  `:page_directory`);;

new_type_abbrev("observable_pages_k",
  `:observable_pages`);;

new_type_abbrev("region_handles_k",
  `:region_state`);;

new_type_abbrev("observable_pages_u",
  `:observable_pages`);;

let (view_induct,view_recursion) =
  let (induct,recursion) = define_type
    "view =
       EView
         observable_pages_e
     | HView
         current_page_directory_h
         pages_h
         region_handles_h
         reference_page_directory_h
     | KView
         observable_pages_k
         region_handles_k
     | UView
         observable_pages_u" in
  let induct' = prove
    (`!phi.
        (!f. phi (EView f)) /\
        (!c p g r. phi (HView c p g r)) /\
        (!f g. phi (KView f g)) /\
        (!f. phi (UView f)) ==>
        !v. phi v`,
     ACCEPT_TAC induct)
  and recursion' = prove
    (`!fe fh fk fu.
        ?(fn : view -> A).
          (!f. fn (EView f) = fe f) /\
          (!c p g r. fn (HView c p g r) = fh c p g r) /\
          (!f g. fn (KView f g) = fk f g) /\
          (!f. fn (UView f) = fu f)`,
     MATCH_ACCEPT_TAC recursion) in
  (induct',recursion');;

export_thm view_induct;;
export_thm view_recursion;;

(* The view of the environment domain *)

let observable_pages_e_def = new_recursive_definition view_recursion
  `!f. observable_pages_e (EView f) = f`;;

export_thm observable_pages_e_def;;

let mk_observable_pages_e_def = new_definition
  `mk_observable_pages_e =
   translate_to_observable_pages
     (\s vpa.
        case_option
          NONE
          (\ppa. if is_environment (status s ppa) then SOME ppa else NONE)
          (translate_page s (cr3 s) vpa))`;;

export_thm mk_observable_pages_e_def;;

(* The view of the H domain *)

let current_page_directory_h_def = new_recursive_definition view_recursion
  `!c p g r. current_page_directory_h (HView c p g r) = c`;;

export_thm current_page_directory_h_def;;

let pages_h_def = new_recursive_definition view_recursion
  `!c p g r. pages_h (HView c p g r) = p`;;

export_thm pages_h_def;;

let region_handles_h_def = new_recursive_definition view_recursion
  `!c p g r. region_handles_h (HView c p g r) = g`;;

export_thm region_handles_h_def;;

let reference_page_directory_h_def = new_recursive_definition view_recursion
  `!c p g r. reference_page_directory_h (HView c p g r) = r`;;

export_thm reference_page_directory_h_def;;

let mk_current_page_directory_h_def = new_definition
  `mk_current_page_directory_h = cr3`;;

export_thm mk_current_page_directory_h_def;;

let mk_pages_h_def = new_definition
  `!s ppa.
     mk_pages_h s ppa =
     let page = status s ppa in
     if is_normal page then NONE else SOME page`;;

export_thm mk_pages_h_def;;

let mk_region_handles_h_def = new_definition
  `mk_region_handles_h = regions`;;

export_thm mk_region_handles_h_def;;

let mk_reference_page_directory_h_def = new_definition
  `mk_reference_page_directory_h = reference`;;

export_thm mk_reference_page_directory_h_def;;

(* The view of the kernel domain *)

let observable_pages_k_def = new_recursive_definition view_recursion
  `!f g. observable_pages_k (KView f g) = f`;;

export_thm observable_pages_k_def;;

let region_handles_k_def = new_recursive_definition view_recursion
  `!f g. region_handles_k (KView f g) = g`;;

export_thm region_handles_k_def;;

let mk_observable_pages_k_def = new_definition
  `mk_observable_pages_k =
   translate_to_observable_pages
     (\s vpa. translate_page s (cr3 s) vpa)`;;

export_thm mk_observable_pages_k_def;;

let mk_region_handles_k_def = new_definition
  `mk_region_handles_k = regions`;;

export_thm mk_region_handles_k_def;;

(* The view of the user domain *)

let observable_pages_u_def = new_recursive_definition view_recursion
  `!f. observable_pages_u (UView f) = f`;;

export_thm observable_pages_u_def;;

let mk_observable_pages_u_def = new_definition
  `mk_observable_pages_u =
   translate_to_observable_pages
     (\s vpa.
        if is_user_page_address vpa then translate_page s (cr3 s) vpa
        else NONE)`;;

export_thm mk_observable_pages_u_def;;

(* A type of domain view *)

let view_def = new_recursive_definition domain_recursion
  `(!s.
      view EDomain s =
      EView
        (mk_observable_pages_e s)) /\
   (!s.
      view HDomain s =
      HView
        (mk_current_page_directory_h s)
        (mk_pages_h s)
        (mk_region_handles_h s)
        (mk_reference_page_directory_h s)) /\
   (!s.
      view KDomain s =
      KView
        (mk_observable_pages_k s)
        (mk_region_handles_k s)) /\
   (!s.
      view UDomain s =
      UView
        (mk_observable_pages_u s))`;;

export_thm view_def;;

let view_equiv_def = new_definition
  `!d s t. view_equiv d s t <=> view d s = view d t`;;

export_thm view_equiv_def;;

(* ~~~~~~~ *)
(* Actions *)
(* ~~~~~~~ *)

(* A type of actions *)

let (action_induct,action_recursion) =
  let (induct,recursion) = define_type
    "action =
       WriteE virtual_address byte
     | DeriveRegionH physical_region physical_page_address region_length
     | AllocatePageDirectoryH physical_page_address
     | FreePageDirectoryH page_directory
     | AddMappingH
         page_directory (physical_page_address list)
         physical_region virtual_region
     | RemoveMappingH page_directory virtual_region
     | AddKernelMappingH physical_region virtual_region
     | ExecuteH page_directory
     | WriteK virtual_address byte
     | WriteU virtual_address byte" in
  let induct' = prove
    (`!p.
        (!va b. p (WriteE va b)) /\
        (!pr ppa l. p (DeriveRegionH pr ppa l)) /\
        (!ppa. p (AllocatePageDirectoryH ppa)) /\
        (!pd. p (FreePageDirectoryH pd)) /\
        (!pd pts pr vr. p (AddMappingH pd pts pr vr)) /\
        (!pd vr. p (RemoveMappingH pd vr)) /\
        (!pr vr. p (AddKernelMappingH pr vr)) /\
        (!pd. p (ExecuteH pd)) /\
        (!va b. p (WriteK va b)) /\
        (!va b. p (WriteU va b)) ==>
        !a. p a`,
     ACCEPT_TAC induct)
  and recursion' = prove
    (`!fwe fdr fapd ffpd fam frm fakm fe fwk fwu.
        ?(fn : action -> A).
          (!va b. fn (WriteE va b) = fwe va b) /\
          (!pr ppa l. fn (DeriveRegionH pr ppa l) = fdr pr ppa l) /\
          (!ppa. fn (AllocatePageDirectoryH ppa) = fapd ppa) /\
          (!pd. fn (FreePageDirectoryH pd) = ffpd pd) /\
          (!pd pts pr vr. fn (AddMappingH pd pts pr vr) = fam pd pts pr vr) /\
          (!pd vr. fn (RemoveMappingH pd vr) = frm pd vr) /\
          (!pr vr. fn (AddKernelMappingH pr vr) = fakm pr vr) /\
          (!pd. fn (ExecuteH pd) = fe pd) /\
          (!va b. fn (WriteK va b) = fwk va b) /\
          (!va b. fn (WriteU va b) = fwu va b)`,
     MATCH_ACCEPT_TAC recursion) in
  (induct',recursion');;

export_thm action_induct;;
export_thm action_recursion;;

let domain_def = new_recursive_definition action_recursion
  `(!va b. domain (WriteE va b) = EDomain) /\
   (!pr ppa l. domain (DeriveRegionH pr ppa l) = HDomain) /\
   (!ppa. domain (AllocatePageDirectoryH ppa) = HDomain) /\
   (!pd. domain (FreePageDirectoryH pd) = HDomain) /\
   (!pd pts pr vr. domain (AddMappingH pd pts pr vr) = HDomain) /\
   (!pd vr. domain (RemoveMappingH pd vr) = HDomain) /\
   (!pr vr. domain (AddKernelMappingH pr vr) = HDomain) /\
   (!pd. domain (ExecuteH pd) = HDomain) /\
   (!va b. domain (WriteK va b) = KDomain) /\
   (!va b. domain (WriteU va b) = UDomain)`;;

export_thm domain_def;;

let write_e_def = new_definition
  `!va b s s'.
     write_e va b s s' <=>
     cr3 s = cr3 s' /\
     reference s = reference s' /\
     regions s = regions s' /\
     case_option
       F
       (\pa.
          let (ppa,i) = dest_physical_address pa in
          !ppa'.
            if ppa' = ppa then
              case_option
                F
                (\d.
                   dest_environment (status s' ppa') =
                   SOME (update_page_data i b d))
                (dest_environment (status s ppa'))
            else
              status s ppa' = status s' ppa')
       (translation s va)`;;

export_thm write_e_def;;

let derive_region_h_def = new_definition
  `!pr ppa l s s'.
     derive_region_h pr ppa l s s' <=>
     cr3 s = cr3 s' /\
     reference s = reference s' /\
     status s = status s' /\
     initial_regions (regions s) = initial_regions (regions s') /\
     let r = PhysicalRegion ppa l in
     is_physical_subregion r pr /\
     ~(r IN all_regions (regions s)) /\
     all_regions (regions s') = r INSERT all_regions (regions s)`;;

export_thm derive_region_h_def;;

let allocate_page_directory_h_def = new_definition
  `!ppa s s'.
     allocate_page_directory_h ppa s s' <=>
     cr3 s = cr3 s' /\
     reference s = reference s' /\
     regions s = regions s' /\
     unmapped_normal_page s ppa /\
     !ppa'.
       status s' ppa' =
       status s (if ppa' = ppa then reference s else ppa')`;;

export_thm allocate_page_directory_h_def;;

let free_page_directory_h_def = new_definition
  `!pd s s'.
     free_page_directory_h pd s s' <=>
     allocate_page_directory_h pd s' s /\
     status s' pd = Normal zero_page_data`;;

export_thm free_page_directory_h_def;;

let add_mapping_def = new_definition
  `!pd pts pr vr s s'.
     add_mapping pd pts pr vr s s' <=>
     cr3 s = cr3 s' /\
     reference s = reference s' /\
     regions s = regions s' /\
     is_page_directory (status s pd) /\
     (!pt. pt IN pts ==> unmapped_normal_page s pt) /\
     (!pt. pt IN pts ==> ~member_physical_region pt pr) /\
     forall_physical_region (is_normal_page s) pr /\
     physical_region_length pr = virtual_region_length vr /\
     is_user_region vr /\
     (!vpa.
        if member_virtual_region vpa vr then
          is_none (translate_page s pd vpa)
        else
          translate_page s' pd vpa = translate_page s pd vpa) /\
     ALL I (zipwith (\vpa ppa. translate_page s' pd vpa = SOME ppa)
              (virtual_region_to_list vr) (physical_region_to_list pr)) /\
     !ppa.
       if ppa IN pts then
         table_mapped_in_directory s' pd ppa
       else if ppa = pd then
         is_page_directory (status s' ppa)
       else if table_mapped_in_directory s pd ppa then
         is_page_table (status s' ppa)
       else
         status s ppa = status s' ppa`;;

export_thm add_mapping_def;;

let add_mapping_h_def = new_definition
  `!pd pts pr vr s s'.
     add_mapping_h pd pts pr vr s s' <=>
     LENGTH (nub pts) = LENGTH pts /\
     pr IN all_regions (regions s) /\
     ?n.
       n <= LENGTH pts /\
       add_mapping pd (set_of_list (take n pts)) pr vr s s'`;;

export_thm add_mapping_h_def;;

let remove_mapping_h_def = new_definition
  `!pd vr s s'.
     remove_mapping_h pd vr s s' <=>
     case_option
       F
       (\prs.
          let pr = PhysicalRegion prs (virtual_region_length vr) in
          let pts = { ppa | is_page_table (status s ppa) /\
                            status s' ppa = Normal zero_page_data } in
          add_mapping pd pts pr vr s' s)
       (translate_page s pd (virtual_region_start vr))`;;

export_thm remove_mapping_h_def;;

let add_kernel_mapping_h_def = new_definition
  `!pr vr s s'.
     add_kernel_mapping_h pr vr s s' <=>
     cr3 s = cr3 s' /\
     reference s = reference s' /\
     regions s = regions s' /\
     pr IN all_regions (regions s) /\
     forall_physical_region (is_normal_page s) pr /\
     physical_region_length pr = virtual_region_length vr /\
     is_kernel_region vr /\
     (!vpa.
        ~member_virtual_region vpa vr ==>
        translate_page s' (reference s') vpa =
        translate_page s (reference s) vpa) /\
     forall_virtual_region
       (\vpa.
           case_option T (\ppa. ~is_environment_page s ppa)
             (translate_page s (reference s) vpa)) vr /\
     ALL I (zipwith (\vpa ppa. translate_page s' (reference s') vpa = SOME ppa)
              (virtual_region_to_list vr) (physical_region_to_list pr)) /\
     !ppa.
       if table_mapped_in_directory s (reference s) ppa then
         is_page_table (status s' ppa)
       else
         status s ppa = status s' ppa`;;

export_thm add_kernel_mapping_h_def;;

let execute_h_def = new_definition
  `!pd s s'.
     execute_h pd s s' <=>
     reference s = reference s' /\
     status s = status s' /\
     regions s = regions s' /\
     cr3 s' = pd`;;

export_thm execute_h_def;;

let write_k_def = new_definition
  `!va b s s'.
     write_k va b s s' <=>
     cr3 s = cr3 s' /\
     reference s = reference s' /\
     regions s = regions s' /\
     is_kernel_address va /\
     case_option
       F
       (\pa.
          let (ppa,i) = dest_physical_address pa in
          !ppa'.
            if ppa' = ppa then
              case_option
                F
                (\d.
                   dest_normal (status s' ppa') =
                   SOME (update_page_data i b d))
                (dest_normal (status s ppa'))
            else
              status s ppa' = status s' ppa')
       (translation s va)`;;

export_thm write_k_def;;

let write_u_def = new_definition
  `!va b s s'.
     write_u va b s s' <=>
     cr3 s = cr3 s' /\
     reference s = reference s' /\
     regions s = regions s' /\
     is_user_address va /\
     case_option
       F
       (\pa.
          let (ppa,i) = dest_physical_address pa in
          !ppa'.
            if ppa' = ppa then
              case_option
                F
                (\d.
                   dest_normal (status s' ppa') =
                   SOME (update_page_data i b d))
                (dest_normal (status s ppa'))
            else
              status s ppa' = status s' ppa')
       (translation s va)`;;

export_thm write_u_def;;

let action_spec_def = new_recursive_definition action_recursion
  `(!va b.
      action_spec (WriteE va b) =
      write_e va b) /\
   (!pr ppa l.
      action_spec (DeriveRegionH pr ppa l) =
      derive_region_h pr ppa l) /\
   (!ppa.
      action_spec (AllocatePageDirectoryH ppa) =
      allocate_page_directory_h ppa) /\
   (!pd.
      action_spec (FreePageDirectoryH pd) =
      free_page_directory_h pd) /\
   (!pd pts pr vr.
      action_spec (AddMappingH pd pts pr vr) =
      add_mapping_h pd pts pr vr) /\
   (!pd vr.
      action_spec (RemoveMappingH pd vr) =
      remove_mapping_h pd vr) /\
   (!pr vr.
      action_spec (AddKernelMappingH pr vr) =
      add_kernel_mapping_h pr vr) /\
   (!pd.
      action_spec (ExecuteH pd) =
      execute_h pd) /\
   (!va b.
      action_spec (WriteK va b) =
      write_k va b) /\
   (!va b.
      action_spec (WriteU va b) =
      write_u va b)`;;

export_thm action_spec_def;;

let action_def = new_definition
  `!a s s'.
      action a s s' <=> wellformed s /\ wellformed s' /\ action_spec a s s'`;;

export_thm action_def;;

(* ~~~~~~ *)
(* Output *)
(* ~~~~~~ *)

let output_tybij =
  define_newtype ("x","output")
    ("v", `:view`);;

export_thm output_tybij;;

let output_def = new_definition
  `!a s. output a s = mk_output (view (domain a) s)`;;

export_thm output_def;;

(* ~~~~~~~~~~~~~~~~~~~~~~ *)
(* System security policy *)
(* ~~~~~~~~~~~~~~~~~~~~~~ *)

let interferes_def = new_definition
  `interferes x y <=>
   (x = EDomain /\ y = EDomain) \/
   (x = EDomain /\ y = HDomain) \/
   (x = EDomain /\ y = KDomain) \/
   (x = HDomain /\ y = HDomain) \/
   (x = HDomain /\ y = KDomain) \/
   (x = HDomain /\ y = UDomain) \/
   (x = KDomain /\ y = KDomain) \/
   (x = KDomain /\ y = UDomain) \/
   (x = UDomain /\ y = KDomain) \/
   (x = UDomain /\ y = UDomain)`;;

export_thm interferes_def;;

(* ------------------------------------------------------------------------- *)
(* Proof of memory safety for the H interface.                               *)
(* ------------------------------------------------------------------------- *)

export_theory "h-thm";;

(* ~~~~~~~~~~~~~~ *)
(* Region lengths *)
(* ~~~~~~~~~~~~~~ *)

(* ~~~~~~~~~~~~~~~ *)
(* Address offsets *)
(* ~~~~~~~~~~~~~~~ *)

(* ~~~~~~~~~~~~~~~~~~ *)
(* Physical addresses *)
(* ~~~~~~~~~~~~~~~~~~ *)

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Regions of physical memory *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let physical_region_cases = prove_cases_thm physical_region_induct;;

export_thm physical_region_cases;;

let physical_region_cases_tac = CASES_TAC physical_region_cases;;

let physical_region_inj =
    prove_constructors_injective physical_region_recursion;;

let length_physical_region_to_list = prove
  (`!pr.
      LENGTH (physical_region_to_list pr) =
      dest_region_length (physical_region_length pr)`,
   GEN_TAC THEN
   physical_region_cases_tac `pr : physical_region` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [physical_region_to_list_def; LENGTH_MAP; length_interval;
      physical_region_length_def]);;

export_thm length_physical_region_to_list;;

(* ~~~~~~~~~~~~~~~~~ *)
(* Virtual addresses *)
(* ~~~~~~~~~~~~~~~~~ *)

let virtual_superpage_address_cases = prove
  (`!vsa. ?w. vsa = mk_virtual_superpage_address w`,
   GEN_TAC THEN
   EXISTS_TAC `dest_virtual_superpage_address vsa` THEN
   REWRITE_TAC [virtual_superpage_address_tybij]);;

let virtual_superpage_address_cases_tac =
    CASES_TAC virtual_superpage_address_cases;;

let virtual_page_address_cases = prove
  (`!vpa. ?vsa si. vpa = mk_virtual_page_address (vsa,si)`,
   GEN_TAC THEN
   EXISTS_TAC `FST (dest_virtual_page_address vpa)` THEN
   EXISTS_TAC `SND (dest_virtual_page_address vpa)` THEN
   REWRITE_TAC [PAIR; virtual_page_address_tybij]);;

let virtual_page_address_cases_tac =
    CASES_TAC virtual_page_address_cases;;

let virtual_address_cases = prove
  (`!va. ?vpa i. va = mk_virtual_address (vpa,i)`,
   GEN_TAC THEN
   EXISTS_TAC `FST (dest_virtual_address va)` THEN
   EXISTS_TAC `SND (dest_virtual_address va)` THEN
   REWRITE_TAC [PAIR; virtual_address_tybij]);;

let virtual_address_cases_tac =
    CASES_TAC virtual_address_cases;;

let mk_virtual_address_inj = prove
  (`!r1 r2. mk_virtual_address r1 = mk_virtual_address r2 <=> r1 = r2`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    ONCE_REWRITE_TAC [GSYM virtual_address_tybij] THEN
    ASM_REWRITE_TAC [];
    DISCH_THEN SUBST1_TAC THEN
    REFL_TAC]);;

(* ~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Regions of virtual memory *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let virtual_region_cases = prove_cases_thm virtual_region_induct;;

export_thm virtual_region_cases;;

let virtual_region_cases_tac = CASES_TAC virtual_region_cases;;

let virtual_region_inj =
    prove_constructors_injective virtual_region_recursion;;

let length_virtual_region_to_list = prove
  (`!vr.
      LENGTH (virtual_region_to_list vr) =
      dest_region_length (virtual_region_length vr)`,
   GEN_TAC THEN
   virtual_region_cases_tac `vr : virtual_region` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [virtual_region_to_list_def; LENGTH_MAP; length_interval;
      virtual_region_length_def]);;

export_thm length_virtual_region_to_list;;

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* User and kernel virtual addresses *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let kernel_page_address_not_user = prove
  (`!vpa. is_kernel_page_address vpa <=> ~is_user_page_address vpa`,
   REWRITE_TAC [is_user_page_address_def]);;

export_thm kernel_page_address_not_user;;

let user_kernel_boundary = prove
  (`!n.
      n < 768 ==>
      is_user_superpage_address (num_to_virtual_superpage_address n)`,
   GEN_TAC THEN
   SUBGOAL_THEN `768 < word10_size` ASSUME_TAC THENL
   [REWRITE_TAC [word10_size_def; word10_width_def] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   STRIP_TAC THEN
   REWRITE_TAC
     [is_user_superpage_address_def; is_kernel_superpage_address_def;
      LET_DEF; LET_END_DEF; num_to_virtual_superpage_address_def;
      virtual_superpage_address_tybij] THEN
   MP_TAC (SPEC `n : num` num_to_word10_to_num_bound) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC LT_TRANS THEN
    EXISTS_TAC `768` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (fun th -> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [SYM th])) THEN
   MP_TAC (SPEC `768` num_to_word10_to_num_bound) THEN
   ANTS_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   POP_ASSUM (K ALL_TAC) THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [GSYM word10_lt_def] THEN
   MP_TAC (SPEC `num_to_word10 n` word10_list_cases) THEN
   STRIP_TAC THEN
   POP_ASSUM SUBST1_TAC THEN
   bit_blast_tac THEN
   REWRITE_TAC [DE_MORGAN_THM]);;

export_thm user_kernel_boundary;;

let is_kernel_region = prove
  (`!vr vpa.
      is_kernel_region vr /\
      member_virtual_region vpa vr ==>
      is_kernel_page_address vpa`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC
     [is_kernel_region_def; forall_virtual_region_def;
      member_virtual_region_def; GSYM ALL_MEM] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm is_kernel_region;;

let is_user_region = prove
  (`!vr vpa.
      is_user_region vr /\
      member_virtual_region vpa vr ==>
      is_user_page_address vpa`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC
     [is_user_region_def; forall_virtual_region_def;
      member_virtual_region_def; GSYM ALL_MEM] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm is_user_region;;

(* ~~~~~~~~~ *)
(* Page data *)
(* ~~~~~~~~~ *)

(* ~~~~~~~~~~~ *)
(* Page tables *)
(* ~~~~~~~~~~~ *)

(* ~~~~~~~~~~~~~~~~ *)
(* Page directories *)
(* ~~~~~~~~~~~~~~~~ *)

let page_directory_entry_cases = prove
  (`!pde. (?psa. pde = Superpage psa) \/ (?pt. pde = Table pt)`,
   ACCEPT_TAC (prove_cases_thm page_directory_entry_induct));;

export_thm page_directory_entry_cases;;

let page_directory_entry_cases_tac = CASES_TAC page_directory_entry_cases;;

let page_directory_entry_distinct =
    prove_constructors_distinct page_directory_entry_recursion;;

let page_directory_entry_inj =
    prove_constructors_injective page_directory_entry_recursion;;

let page_directory_data_cases = prove
  (`!pdd. ?f. pdd = mk_page_directory_data f`,
   STRIP_TAC THEN
   EXISTS_TAC `dest_page_directory_data pdd` THEN
   REWRITE_TAC [page_directory_data_tybij]);;

export_thm page_directory_data_cases;;

let page_directory_data_cases_tac = CASES_TAC page_directory_data_cases;;

(* ~~~~~~~~~~ *)
(* Page types *)
(* ~~~~~~~~~~ *)

let page_cases = prove
  (`!p.
      (?d. p = Environment d) \/
      (?d. p = Normal d) \/
      (?pdd. p = PageDirectory pdd) \/
      (?ptd. p = PageTable ptd) \/
      p = NotInstalled`,
   ACCEPT_TAC (prove_cases_thm page_induct));;

export_thm page_cases;;

let page_cases_tac = CASES_TAC page_cases;;

let page_distinct = prove_constructors_distinct page_recursion;;

let page_inj = prove_constructors_injective page_recursion;;

let dest_environment_or_normal_environment = prove
  (`!p.
      is_environment p ==>
      dest_environment_or_normal p = dest_environment p`,
   STRIP_TAC THEN
   page_cases_tac `p : page` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
      [is_environment_def; dest_environment_def;
       dest_environment_or_normal_def; is_some_def]);;

export_thm dest_environment_or_normal_environment;;

(* ~~~~~~~~~~~~~~~~~~~~~~~ *)
(* The state of the system *)
(* ~~~~~~~~~~~~~~~~~~~~~~~ *)

let region_state_cases = prove_cases_thm region_state_induct;;

export_thm region_state_cases;;

let region_state_inj =
    prove_constructors_injective region_state_recursion;;

let state_cases = prove_cases_thm state_induct;;

export_thm state_cases;;

let state_inj = prove_constructors_injective state_recursion;;

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Virtual to physical mappings *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let translate_page_eq = prove
  (`!s s'.
      (!pd vpa.
         translate_page s pd vpa =
         translate_page s' pd vpa) ==>
      translate_page s = translate_page s'`,
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [FUN_EQ_THM]);;

export_thm translate_page_eq;;

let translate_page_is_page_directory = prove
  (`!s pd vpa.
      is_some (translate_page s pd vpa) ==>
      is_page_directory (status s pd)`,
   REPEAT GEN_TAC THEN
   virtual_page_address_cases_tac `vpa : virtual_page_address` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [translate_page_def; virtual_page_address_tybij] THEN
   REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
   page_cases_tac `status s pd` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [dest_page_directory_def; is_page_directory_def; is_some_def;
      case_option_def]);;

export_thm translate_page_is_page_directory;;

let translate_page_is_not_page_directory = prove
  (`!s pd vpa.
      ~is_page_directory (status s pd) ==>
      translate_page s pd vpa = NONE`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`s : state`; `pd : page_directory`;
                  `vpa : virtual_page_address`]
              translate_page_is_page_directory) THEN
   option_cases_tac `translate_page s pd vpa` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [is_some_def]);;

export_thm translate_page_is_not_page_directory;;

let translate_page_inj = prove
  (`!s s'.
      (!ppa.
         is_page_directory_or_table (status s ppa) \/
         is_page_directory_or_table (status s' ppa) ==>
         status s ppa = status s' ppa) ==>
      translate_page s = translate_page s'`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   X_GEN_TAC `pd : page_directory` THEN
   X_GEN_TAC `vpa : virtual_page_address` THEN
   virtual_page_address_cases_tac `vpa : virtual_page_address` THEN
   STRIP_TAC THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   ASM_REWRITE_TAC
     [translate_page_def; virtual_page_address_tybij; LET_DEF;
      LET_END_DEF] THEN
   POP_ASSUM
     (fun th ->
        MP_TAC (SPEC `pd : page_directory` th) THEN
        ASSUME_TAC th) THEN
   REWRITE_TAC [is_page_directory_or_table_def; is_page_directory_def] THEN
   page_cases_tac `status s pd` THEN
   STRIP_TAC THEN
   page_cases_tac `status s' pd` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [dest_page_directory_def; is_some_def; case_option_def; page_distinct;
      page_inj] THEN
   DISCH_THEN (SUBST_VAR_TAC o SYM) THEN
   option_cases_tac `dest_page_directory_data pdd vsa` THENL
   [STRIP_TAC THEN
    ASM_REWRITE_TAC [case_option_def];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `pde : page_directory_entry` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   page_directory_entry_cases_tac `pde : page_directory_entry` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_page_directory_entry_def] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `pt : page_table`) THEN
   REWRITE_TAC [is_page_directory_or_table_def; is_page_table_def] THEN
   page_cases_tac `status s pt` THEN
   STRIP_TAC THEN
   page_cases_tac `status s' pt` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [dest_page_table_def; is_some_def; case_option_def; page_distinct;
      page_inj] THEN
   DISCH_THEN (SUBST_VAR_TAC o SYM) THEN
   REFL_TAC);;

export_thm translate_page_inj;;

let status_translate_page = prove
  (`!s s'.
      status s = status s' ==>
      translate_page s = translate_page s'`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC translate_page_inj THEN
   ASM_REWRITE_TAC []);;

export_thm status_translate_page;;

let unmapped_normal_page_unmapped = prove
  (`!s ppa. unmapped_normal_page s ppa ==> unmapped_page s ppa`,
   REWRITE_TAC [unmapped_normal_page_def] THEN
   REPEAT STRIP_TAC);;

export_thm unmapped_normal_page_unmapped;;

let unmapped_normal_page_normal = prove
  (`!s ppa. unmapped_normal_page s ppa ==> is_normal_page s ppa`,
   REWRITE_TAC [unmapped_normal_page_def] THEN
   REPEAT STRIP_TAC);;

export_thm unmapped_normal_page_normal;;

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Well-formed machine states *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let cr3_is_page_directory = prove
  (`!s. wellformed s ==> is_page_directory (status s (cr3 s))`,
   REWRITE_TAC [wellformed_def] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `s : state` cr3_is_page_directory_def) THEN
   ASM_REWRITE_TAC []);;

export_thm cr3_is_page_directory;;

let reference_is_page_directory = prove
  (`!s. wellformed s ==> is_page_directory (status s (reference s))`,
   REWRITE_TAC [wellformed_def] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `s : state` reference_is_page_directory_def) THEN
   ASM_REWRITE_TAC []);;

export_thm reference_is_page_directory;;

let environment_only_kernel_addresses = prove
  (`!s pd vpa ppa.
      wellformed s /\
      translate_page s pd vpa = SOME ppa /\
      is_environment (status s ppa) ==>
      is_kernel_page_address vpa`,
   REWRITE_TAC [wellformed_def] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `s : state` reference_maps_kernel_addresses_def) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   MP_TAC (SPEC `s : state` environment_only_in_reference_def) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL [`pd : page_directory`;
                               `vpa : virtual_page_address`]) THEN
   ASM_REWRITE_TAC [case_option_def]);;

export_thm environment_only_kernel_addresses;;

let dest_environment_or_normal_user_addresses = prove
  (`!s pd vpa ppa.
      wellformed s /\
      is_user_page_address vpa /\
      translate_page s pd vpa = SOME ppa ==>
      dest_environment_or_normal (status s ppa) = dest_normal (status s ppa)`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `~is_environment (status s ppa)` MP_TAC THENL
   [UNDISCH_TAC `is_user_page_address vpa` THEN
    REWRITE_TAC [is_user_page_address_def; CONTRAPOS_THM] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC environment_only_kernel_addresses THEN
    EXISTS_TAC `s : state` THEN
    EXISTS_TAC `pd : page_directory` THEN
    EXISTS_TAC `ppa : physical_page_address` THEN
    ASM_REWRITE_TAC [];
    POP_ASSUM_LIST (K ALL_TAC) THEN
    page_cases_tac `status s ppa` THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC
      [is_environment_def; dest_environment_def; dest_normal_def;
       dest_environment_or_normal_def; is_some_def]]);;

export_thm dest_environment_or_normal_user_addresses;;

let page_directories_contain_reference = prove
  (`!s pd vpa.
      wellformed s /\
      is_page_directory (status s pd) /\
      is_kernel_page_address vpa ==>
      translate_page s pd vpa = translate_page s (reference s) vpa`,
   REWRITE_TAC [wellformed_def] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `s : state` page_directories_contain_reference_def) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC []);;

export_thm page_directories_contain_reference;;

let cr3_contains_reference = prove
  (`!s vpa.
      wellformed s /\
      is_kernel_page_address vpa ==>
      translate_page s (cr3 s) vpa = translate_page s (reference s) vpa`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC page_directories_contain_reference THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC cr3_is_page_directory THEN
   ASM_REWRITE_TAC []);;

export_thm cr3_contains_reference;;

let table_pointers_are_page_tables = prove
  (`!s pd pdd pdi pt.
      wellformed s /\
      status s pd = PageDirectory pdd /\
      dest_page_directory_data pdd pdi = SOME (Table pt) ==>
      is_page_table (status s pt)`,
   REWRITE_TAC [wellformed_def] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `s : state` table_pointers_are_page_tables_def) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN
     (MP_TAC o SPECL [`pd : page_directory`; `pdi : page_directory_index`]) THEN
   ASM_REWRITE_TAC
     [dest_page_directory_def; case_option_def;
      case_page_directory_entry_def]);;

export_thm table_pointers_are_page_tables;;

let table_mapped_in_directory = prove
  (`!s pd pt.
     table_mapped_in_directory s pd pt <=>
     ?pdd pdi.
        status s pd = PageDirectory pdd /\
        dest_page_directory_data pdd pdi = SOME (Table pt)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [table_mapped_in_directory_def] THEN
   page_cases_tac `status s pd` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [page_distinct; page_inj; dest_page_directory_def; case_option_def] THEN
   CONV_TAC (RAND_CONV (REWR_CONV SWAP_EXISTS_THM)) THEN
   REWRITE_TAC [UNWIND_THM1]);;

export_thm table_mapped_in_directory;;

let table_mapped_in_directory_is_page_directory_table = prove
  (`!s pd pt.
      wellformed s /\
      table_mapped_in_directory s pd pt ==>
      is_page_directory (status s pd) /\
      is_page_table (status s pt)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [is_page_directory_def; table_mapped_in_directory_def] THEN
   (page_cases_tac `status s pd` THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC
      [dest_page_directory_def; case_option_def; is_some_def]) THEN
   STRIP_TAC THEN
   MATCH_MP_TAC table_pointers_are_page_tables THEN
   EXISTS_TAC `pd : page_directory` THEN
   EXISTS_TAC `pdd : page_directory_data` THEN
   EXISTS_TAC `pdi : page_directory_index` THEN
   ASM_REWRITE_TAC []);;

let table_mapped_in_directory_is_page_directory = prove
  (`!s pd pt.
      wellformed s /\
      table_mapped_in_directory s pd pt ==>
      is_page_directory (status s pd)`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`s : state`; `pd : page_directory`; `pt : page_table`]
             table_mapped_in_directory_is_page_directory_table) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC);;

export_thm table_mapped_in_directory_is_page_directory;;

let table_mapped_in_directory_is_page_table = prove
  (`!s pd pt.
      wellformed s /\
      table_mapped_in_directory s pd pt ==>
      is_page_table (status s pt)`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`s : state`; `pd : page_directory`; `pt : page_table`]
             table_mapped_in_directory_is_page_directory_table) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC);;

export_thm table_mapped_in_directory_is_page_table;;

let no_shared_page_tables = prove
  (`!s pt pd1 pd2 pdd1 pdd2 vsa1 vsa2.
      wellformed s /\
      dest_page_directory (status s pd1) = SOME pdd1 /\
      dest_page_directory (status s pd2) = SOME pdd2 /\
      dest_page_directory_data pdd1 vsa1 = SOME (Table pt) /\
      dest_page_directory_data pdd2 vsa2 = SOME (Table pt) ==>
      vsa1 = vsa2 /\
      (is_kernel_superpage_address vsa1 \/ pd1 = pd2)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [wellformed_def] THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `s : state` no_shared_page_tables_def) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   EXISTS_TAC `pt : page_table` THEN
   EXISTS_TAC `pdd1 : page_directory_data` THEN
   EXISTS_TAC `pdd2 : page_directory_data` THEN
   ASM_REWRITE_TAC []);;

export_thm no_shared_page_tables;;

let reference_maps_kernel_addresses = prove
  (`!s vpa.
      wellformed s /\
      mapped_page s (reference s) vpa ==>
      is_kernel_page_address vpa`,
   REWRITE_TAC [wellformed_def] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `s : state` reference_maps_kernel_addresses_def) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm reference_maps_kernel_addresses;;

(* ~~~~~~~~~~~~~~~~ *)
(* Observable pages *)
(* ~~~~~~~~~~~~~~~~ *)

let mk_observable_pages_inj = prove
  (`!f1 f2.
      mk_observable_pages f1 = mk_observable_pages f2 <=>
      !vpa. f1 vpa = f2 vpa`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [GSYM FUN_EQ_THM] THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    ONCE_REWRITE_TAC [GSYM observable_pages_tybij] THEN
    ASM_REWRITE_TAC [];
    DISCH_THEN SUBST1_TAC THEN
    REFL_TAC]);;

export_thm mk_observable_pages_inj;;

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Protection domains and their view of the system state *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let domain_cases = prove_cases_thm domain_induct;;

export_thm domain_cases;;

let domain_distinct = prove_constructors_distinct domain_recursion;;

let action_cases = prove_cases_thm action_induct;;

export_thm action_cases;;

let action_distinct = prove_constructors_distinct action_recursion;;

let action_inj = prove_constructors_injective action_recursion;;

let view_e_recursion = prove
  (`!fe. ?fn. !f. fn (EView f) = (fe f : A)`,
   GEN_TAC THEN
   MP_TAC
     (SPECL
        [`fe : observable_pages_e -> A`;
         `fh : current_page_directory_h -> pages_h -> region_handles_h ->
               reference_page_directory_h -> A`;
         `fk : observable_pages_k -> region_handles_k -> A`;
         `fu : observable_pages_u -> A`]
        view_recursion) THEN
   STRIP_TAC THEN
   EXISTS_TAC `fn : view -> A` THEN
   FIRST_ASSUM ACCEPT_TAC);;

let view_h_recursion = prove
  (`!fh. ?fn. !c p g r. fn (HView c p g r) = (fh c p g r : A)`,
   GEN_TAC THEN
   MP_TAC
     (SPECL
        [`fe : observable_pages_e -> A`;
         `fh : current_page_directory_h -> pages_h -> region_handles_h ->
               reference_page_directory_h -> A`;
         `fk : observable_pages_k -> region_handles_k -> A`;
         `fu : observable_pages_u -> A`]
        view_recursion) THEN
   STRIP_TAC THEN
   EXISTS_TAC `fn : view -> A` THEN
   FIRST_ASSUM ACCEPT_TAC);;

let view_k_recursion = prove
  (`!fk. ?fn. !f g. fn (KView f g) = (fk f g : A)`,
   GEN_TAC THEN
   MP_TAC
     (SPECL
        [`fe : observable_pages_e -> A`;
         `fh : current_page_directory_h -> pages_h -> region_handles_h ->
               reference_page_directory_h -> A`;
         `fk : observable_pages_k -> region_handles_k -> A`;
         `fu : observable_pages_u -> A`]
        view_recursion) THEN
   STRIP_TAC THEN
   EXISTS_TAC `fn : view -> A` THEN
   FIRST_ASSUM ACCEPT_TAC);;

let view_u_recursion = prove
  (`!fu. ?fn. !f. fn (UView f) = (fu f : A)`,
   GEN_TAC THEN
   MP_TAC
     (SPECL
        [`fe : observable_pages_e -> A`;
         `fh : current_page_directory_h -> pages_h -> region_handles_h ->
               reference_page_directory_h -> A`;
         `fk : observable_pages_k -> region_handles_k -> A`;
         `fu : observable_pages_u -> A`]
        view_recursion) THEN
   STRIP_TAC THEN
   EXISTS_TAC `fn : view -> A` THEN
   FIRST_ASSUM ACCEPT_TAC);;

let view_cases = prove_cases_thm view_induct;;

export_thm view_cases;;

let view_distinct = prove_constructors_distinct view_recursion;;

let view_inj = prove_constructors_injective view_recursion;;

export_thm view_inj;;

let view_equiv_refl = prove
  (`!d s. view_equiv d s s`,
   REWRITE_TAC [view_equiv_def]);;

export_thm view_equiv_refl;;

let view_equiv_symm = prove
  (`!d s t. view_equiv d s t ==> view_equiv d t s`,
   REWRITE_TAC [view_equiv_def] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

export_thm view_equiv_symm;;

let view_equiv_trans = prove
  (`!d s1 s2 s3.
      view_equiv d s1 s2 /\ view_equiv d s2 s3 ==>
      view_equiv d s1 s3`,
   REWRITE_TAC [view_equiv_def] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

export_thm view_equiv_trans;;

(* ~~~~~~~ *)
(* Actions *)
(* ~~~~~~~ *)

(* write_e *)

let write_e_status = prove
  (`!s s' va b ppa.
      write_e va b s s' /\
      (~is_environment (status s ppa) \/
       ~is_environment (status s' ppa)) ==>
      status s ppa = status s' ppa`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [write_e_def] THEN
   DISCH_THEN
     (fun th ->
        STRIP_ASSUME_TAC (CONJUNCT1 th) THEN
        MP_TAC (CONJUNCT2 th)) THEN
   POP_ASSUM MP_TAC THEN
   option_cases_tac `translation s va` THENL
   [STRIP_TAC THEN
    ASM_REWRITE_TAC [case_option_def];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `pa : physical_address` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   PAIR_CASES_TAC `dest_physical_address pa` THEN
   DISCH_THEN
    (X_CHOOSE_THEN `ppa' : physical_page_address`
      (X_CHOOSE_THEN `i : page_offset` STRIP_ASSUME_TAC)) THEN
   ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
   DISCH_THEN (MP_TAC o SPEC `ppa : physical_page_address`) THEN
   COND_CASES_TAC THENL
   [POP_ASSUM (SUBST_VAR_TAC o SYM) THEN
    page_cases_tac `status s ppa` THEN
    STRIP_TAC THEN
    page_cases_tac `status s' ppa` THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC
      [is_environment_def; dest_environment_def; case_option_def; page_distinct;
       page_inj; option_distinct; is_some_def];
    DISCH_THEN (fun th -> REWRITE_TAC [th])]);;

export_thm write_e_status;;

let write_e_translate_page = prove
  (`!s s' va b.
      write_e va b s s' ==>
      translate_page s = translate_page s'`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC translate_page_inj THEN
   GEN_TAC THEN
   DISCH_THEN ASSUME_TAC THEN
   MATCH_MP_TAC write_e_status THEN
   EXISTS_TAC `va : virtual_address` THEN
   EXISTS_TAC `b : byte` THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM MP_TAC THEN
   MP_TAC (SPEC `status s ppa` page_cases) THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `status s' ppa` page_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_page_directory_or_table_def; is_page_directory_def;
      is_page_table_def; dest_page_directory_def; is_some_def;
      dest_page_table_def; dest_environment_def; case_option_def; page_distinct;
      page_inj; option_distinct; is_environment_def]);;

export_thm write_e_translate_page;;

let write_e_cr3 = prove
  (`!s s' va b. write_e va b s s' ==> cr3 s = cr3 s'`,
   REWRITE_TAC [write_e_def] THEN
   REPEAT STRIP_TAC);;

export_thm write_e_cr3;;

let write_e_regions = prove
  (`!s s' va b. write_e va b s s' ==> regions s = regions s'`,
   REWRITE_TAC [write_e_def] THEN
   REPEAT STRIP_TAC);;

export_thm write_e_regions;;

let write_e_reference = prove
  (`!s s' va b. write_e va b s s' ==> reference s = reference s'`,
   REWRITE_TAC [write_e_def] THEN
   REPEAT STRIP_TAC);;

export_thm write_e_reference;;

let write_e_translate_page_cr3 = prove
  (`!s s' va b.
      write_e va b s s' ==>
      translate_page s (cr3 s) = translate_page s' (cr3 s')`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_e_translate_page) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_e_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

export_thm write_e_translate_page_cr3;;

let write_e_status_update = prove
  (`!s s' va b.
      write_e va b s s' ==>
      ?vpa i ppa d.
        va = mk_virtual_address (vpa,i) /\
        translate_page s (cr3 s) vpa = SOME ppa /\
        status s ppa = Environment d /\
        !ppa'.
           status s' ppa' =
             if ppa' = ppa then Environment (update_page_data i b d)
             else status s ppa'`,
   REPEAT GEN_TAC THEN
   virtual_address_cases_tac `va : virtual_address` THEN
   REPEAT STRIP_TAC THEN
   EXISTS_TAC `vpa : virtual_page_address` THEN
   EXISTS_TAC `i : page_offset` THEN
   FIRST_ASSUM (MP_TAC o CONV_RULE (REWR_CONV write_e_def)) THEN
   DISCH_THEN (MP_TAC o CONJUNCT2 o REWRITE_RULE [CONJ_ASSOC]) THEN
   ASM_REWRITE_TAC [translation_def; virtual_address_tybij] THEN
   REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
   option_cases_tac `translate_page s (cr3 s) vpa` THENL
   [STRIP_TAC THEN
    ASM_REWRITE_TAC [case_option_def];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `ppa : physical_page_address` ASSUME_TAC) THEN
   ASM_REWRITE_TAC [case_option_def; physical_address_tybij] THEN
   STRIP_TAC THEN
   EXISTS_TAC `ppa : physical_page_address` THEN
   FIRST_ASSUM (MP_TAC o SPEC `ppa : physical_page_address`) THEN
   REWRITE_TAC [] THEN
   page_cases_tac `status s ppa` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_environment_def; dest_environment_def;
      is_normal_def; dest_normal_def;
      is_page_table_def; dest_page_table_def;
      is_page_directory_def; dest_page_directory_def;
      is_some_def; option_distinct; option_inj; case_option_def] THEN
   page_cases_tac `status s' ppa` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_environment_def; dest_environment_def;
      is_normal_def; dest_normal_def;
      is_page_table_def; dest_page_table_def;
      is_page_directory_def; dest_page_directory_def;
      is_some_def; option_distinct; option_inj; case_option_def] THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   EXISTS_TAC `d : page_data` THEN
   REWRITE_TAC [] THEN
   X_GEN_TAC `ppa' : physical_page_address` THEN
   COND_CASES_TAC THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `ppa' : physical_page_address`) THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_ACCEPT_TAC EQ_SYM);;

export_thm write_e_status_update;;

let write_e_is_environment = prove
  (`!s s' va b ppa.
      write_e va b s s' ==>
      is_environment (status s ppa) = is_environment (status s' ppa)`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`s : state`;
         `s' : state`;
         `va : virtual_address`;
         `b : byte`]
        write_e_status_update) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   COND_CASES_TAC THENL
   [ASM_REWRITE_TAC [is_environment_def; dest_environment_def; is_some_def];
    ALL_TAC] THEN
   page_cases_tac `status s ppa` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_environment_def; dest_environment_def;
      is_normal_def; dest_normal_def;
      is_page_table_def; dest_page_table_def;
      is_page_directory_def; dest_page_directory_def;
      is_some_def; option_distinct; option_inj; case_option_def]);;

export_thm write_e_is_environment;;

let write_e_dest_normal = prove
  (`!s s' va b ppa.
      write_e va b s s' ==>
      dest_normal (status s ppa) = dest_normal (status s' ppa)`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`;
             `ppa : physical_page_address`]
      write_e_status) THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC (SPEC `status s ppa` page_cases) THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `status s' ppa` page_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [dest_normal_def; dest_environment_def; case_option_def; page_distinct;
      is_some_def; page_inj; option_distinct; is_environment_def] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

export_thm write_e_dest_normal;;

let write_e_dest_environment_or_normal = prove
  (`!s s' va b pd vpa ppa.
      wellformed s /\
      wellformed s' /\
      is_user_page_address vpa /\
      translate_page s pd vpa = SOME ppa /\
      write_e va b s s' ==>
      dest_environment_or_normal (status s ppa) =
      dest_environment_or_normal (status s' ppa)`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `pd : page_directory`; `vpa : virtual_page_address`;
             `ppa : physical_page_address`]
      dest_environment_or_normal_user_addresses) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL [`s' : state`; `pd : page_directory`; `vpa : virtual_page_address`;
             `ppa : physical_page_address`]
      dest_environment_or_normal_user_addresses) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_e_translate_page) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC write_e_dest_normal THEN
   EXISTS_TAC `va : virtual_address` THEN
   EXISTS_TAC `b : byte` THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm write_e_dest_environment_or_normal;;

let write_e_view_e = prove
  (`!va b. ?f. !s s'.
      wellformed s /\
      wellformed s' /\
      write_e va b s s' ==>
      view EDomain s' = f (view EDomain s)`,
   REPEAT STRIP_TAC THEN
   REPEAT GEN_TAC THEN
   virtual_address_cases_tac `va : virtual_address` THEN
   STRIP_TAC THEN
   REWRITE_TAC [view_def] THEN
   MP_TAC
     (ISPEC
        `\f.
           EView
             (mk_observable_pages
                (\vpa'.
                   case_option
                     NONE
                     (\ (d,vpas).
                        SOME
                          ((if vpa IN vpas then update_page_data i b d else d),
                           vpas))
                     (dest_observable_pages f vpa')))`
        view_e_recursion) THEN
   STRIP_TAC THEN
   EXISTS_TAC `fn : view -> view` THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (CONV_TAC o RAND_CONV o REWR_CONV) THEN
   REWRITE_TAC
     [view_inj; mk_observable_pages_e_def; translate_to_observable_pages_def;
      mk_observable_pages_inj; observable_pages_tybij] THEN
   X_GEN_TAC `vpa' : virtual_page_address` THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_e_translate_page_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MP_TAC
     (SPECL
        [`s : state`;
         `s' : state`;
         `va : virtual_address`;
         `b : byte`]
      write_e_status_update) THEN
   ASM_REWRITE_TAC [mk_virtual_address_inj; PAIR_EQ] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM (SUBST_VAR_TAC o SYM) THEN
   FIRST_X_ASSUM (SUBST_VAR_TAC o SYM) THEN
   ASM_REWRITE_TAC [] THEN
   option_cases_tac `translate_page s (cr3 s) vpa'` THENL
   [DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [case_option_def];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `ppa' : physical_page_address` ASSUME_TAC) THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   ASM_CASES_TAC `ppa' = (ppa : physical_page_address)` THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    ASM_REWRITE_TAC
      [is_environment_def; dest_environment_def; is_some_def;
       case_option_def; dest_environment_or_normal_def; IN_ELIM;
       option_inj; PAIR_EQ; EXTENSION] THEN
    POP_ASSUM (K ALL_TAC) THEN
    X_GEN_TAC `vpa' : virtual_page_address` THEN
    option_cases_tac `translate_page s (cr3 s) vpa'` THENL
    [DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC [case_option_def];
     ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN `ppa' : physical_page_address` ASSUME_TAC) THEN
    ASM_REWRITE_TAC [case_option_def] THEN
    ASM_CASES_TAC `ppa' = (ppa : physical_page_address)` THENL
    [POP_ASSUM SUBST_VAR_TAC THEN
     ASM_REWRITE_TAC
       [is_environment_def; dest_environment_def; is_some_def;
        case_option_def; dest_environment_or_normal_def; IN_ELIM;
        option_inj; PAIR_EQ; EXTENSION];
     ASM_REWRITE_TAC
       [is_environment_def; dest_environment_def; is_some_def;
        case_option_def; dest_environment_or_normal_def; IN_ELIM;
        option_inj; PAIR_EQ; EXTENSION]];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   page_cases_tac `status s ppa'` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_environment_def; dest_environment_def;
      is_normal_def; dest_normal_def; dest_environment_or_normal_def;
      is_page_table_def; dest_page_table_def; IN_ELIM;
      is_page_directory_def; dest_page_directory_def;
      is_some_def; option_distinct; option_inj; case_option_def] THEN
   ASM_REWRITE_TAC [PAIR_EQ; EXTENSION] THEN
   X_GEN_TAC `vpa''' : virtual_page_address` THEN
   ASM_REWRITE_TAC [IN_ELIM] THEN
   option_cases_tac `translate_page s (cr3 s) vpa'''` THENL
   [DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [case_option_def];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `ppa'' : physical_page_address` ASSUME_TAC) THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   ASM_CASES_TAC `ppa'' = (ppa : physical_page_address)` THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    ASM_REWRITE_TAC
      [is_environment_def; dest_environment_def; is_some_def;
       case_option_def; dest_environment_or_normal_def; IN_ELIM;
       option_inj; PAIR_EQ; EXTENSION];
    ALL_TAC] THEN
   ASM_REWRITE_TAC []);;

export_thm write_e_view_e;;

(* derive_region_h *)

let derive_region_h_cr3 = prove
  (`!s s' pr ppa l. derive_region_h pr ppa l s s' ==> cr3 s = cr3 s'`,
   REWRITE_TAC [derive_region_h_def] THEN
   REPEAT STRIP_TAC);;

export_thm derive_region_h_cr3;;

let derive_region_h_status = prove
  (`!s s' pr ppa l. derive_region_h pr ppa l s s' ==> status s = status s'`,
   REWRITE_TAC [derive_region_h_def] THEN
   REPEAT STRIP_TAC);;

export_thm derive_region_h_status;;

let derive_region_h_reference = prove
  (`!s s' pr ppa l.
      derive_region_h pr ppa l s s' ==> reference s = reference s'`,
   REWRITE_TAC [derive_region_h_def] THEN
   REPEAT STRIP_TAC);;

export_thm derive_region_h_reference;;

let derive_region_h_translate_page = prove
  (`!s s' pr ppa l.
      derive_region_h pr ppa l s s' ==>
      translate_page s = translate_page s'`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC status_translate_page THEN
   MATCH_MP_TAC derive_region_h_status THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `ppa : physical_page_address` THEN
   EXISTS_TAC `l : region_length` THEN
   ASM_REWRITE_TAC []);;

export_thm derive_region_h_translate_page;;

let derive_region_h_translate_page_cr3 = prove
  (`!s s' pr ppa l.
      derive_region_h pr ppa l s s' ==>
      translate_page s (cr3 s) = translate_page s' (cr3 s')`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
             `ppa : physical_page_address`; `l : region_length`]
      derive_region_h_translate_page) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
             `ppa : physical_page_address`; `l : region_length`]
      derive_region_h_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

export_thm derive_region_h_translate_page_cr3;;

(* allocate_page_directory_h *)

let allocate_page_directory_h_cr3 = prove
  (`!s s' ppa. allocate_page_directory_h ppa s s' ==> cr3 s = cr3 s'`,
   REWRITE_TAC [allocate_page_directory_h_def] THEN
   REPEAT STRIP_TAC);;

export_thm allocate_page_directory_h_cr3;;

let allocate_page_directory_h_not_cr3 = prove
  (`!s s' ppa.
      wellformed s /\
      allocate_page_directory_h ppa s s' ==>
      ~(cr3 s = ppa)`,
   REPEAT STRIP_TAC THEN
   POP_ASSUM (SUBST_VAR_TAC) THEN
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC
     [allocate_page_directory_h_def; unmapped_normal_page_def;
      is_normal_page_def] THEN
   STRIP_TAC THEN
   POP_ASSUM (K ALL_TAC) THEN
   MP_TAC (SPEC `s : state` cr3_is_page_directory) THEN
   ANTS_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   POP_ASSUM MP_TAC THEN
   POP_ASSUM_LIST (K ALL_TAC) THEN
   page_cases_tac `status s (cr3 s)` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_page_directory_def; is_normal_def;
      dest_page_directory_def; dest_normal_def; is_some_def]);;

export_thm allocate_page_directory_h_not_cr3;;

let allocate_page_directory_h_not_cr3' = prove
  (`!s s' ppa.
      wellformed s /\
      allocate_page_directory_h ppa s s' ==>
      ~(cr3 s' = ppa)`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`s : state`; `s' : state`; `ppa : physical_page_address`]
                 allocate_page_directory_h_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC allocate_page_directory_h_not_cr3 THEN
   EXISTS_TAC `s' : state` THEN
   ASM_REWRITE_TAC []);;

export_thm allocate_page_directory_h_not_cr3';;

let allocate_page_directory_h_reference = prove
  (`!s s' ppa.
      allocate_page_directory_h ppa s s' ==> reference s = reference s'`,
   REWRITE_TAC [allocate_page_directory_h_def] THEN
   REPEAT STRIP_TAC);;

export_thm allocate_page_directory_h_reference;;

let allocate_page_directory_h_regions = prove
  (`!s s' ppa. allocate_page_directory_h ppa s s' ==> regions s = regions s'`,
   REWRITE_TAC [allocate_page_directory_h_def] THEN
   REPEAT STRIP_TAC);;

export_thm allocate_page_directory_h_regions;;

let allocate_page_directory_h_status = prove
  (`!s s' ppa ppa'.
      allocate_page_directory_h ppa s s' /\
      ~(ppa' = ppa) ==>
      status s' ppa' = status s ppa'`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [allocate_page_directory_h_def] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

export_thm allocate_page_directory_h_status;;

let allocate_page_directory_h_dest_environment = prove
  (`!s s' ppa ppa'.
      wellformed s /\
      allocate_page_directory_h ppa s s' ==>
      dest_environment (status s' ppa') = dest_environment (status s ppa')`,
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `ppa' = (ppa : physical_page_address)` THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [allocate_page_directory_h_def; unmapped_normal_page_def] THEN
    DISCH_THEN (STRIP_ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
    POP_ASSUM (STRIP_ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
    ASM_REWRITE_TAC [] THEN
    POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM MP_TAC THEN
    MP_TAC (SPEC `s : state` reference_is_page_directory) THEN
    ASM_REWRITE_TAC [is_normal_page_def] THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN
    page_cases_tac `status s (reference s)` THEN
    STRIP_TAC THEN
    page_cases_tac `status s ppa` THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC
      [is_page_directory_def; is_normal_def; dest_environment_def;
       dest_page_directory_def; dest_normal_def; is_some_def];
    AP_TERM_TAC THEN
    MATCH_MP_TAC allocate_page_directory_h_status THEN
    EXISTS_TAC `ppa : physical_page_address` THEN
    ASM_REWRITE_TAC []]);;

export_thm allocate_page_directory_h_dest_environment;;

let allocate_page_directory_h_is_environment = prove
  (`!s s' ppa ppa'.
      wellformed s /\
      allocate_page_directory_h ppa s s' ==>
      is_environment (status s' ppa') = is_environment (status s ppa')`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [is_environment_def] THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC allocate_page_directory_h_dest_environment THEN
   EXISTS_TAC `ppa : physical_page_address` THEN
   ASM_REWRITE_TAC []);;

export_thm allocate_page_directory_h_is_environment;;

let allocate_page_directory_h_dest_page_table = prove
  (`!s s' ppa pt.
      wellformed s /\
      allocate_page_directory_h ppa s s' ==>
      dest_page_table (status s' pt) = dest_page_table (status s pt)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [allocate_page_directory_h_def; unmapped_normal_page_def] THEN
   DISCH_THEN (STRIP_ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
   POP_ASSUM (STRIP_ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
   ASM_REWRITE_TAC [] THEN
   COND_CASES_TAC THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    UNDISCH_TAC `is_normal_page s ppa` THEN
    MP_TAC (SPEC `s : state` reference_is_page_directory) THEN
    ASM_REWRITE_TAC [is_normal_page_def] THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN
    page_cases_tac `status s (reference s)` THEN
    STRIP_TAC THEN
    page_cases_tac `status s ppa` THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC
      [is_page_directory_def; is_normal_def; dest_page_table_def;
       dest_page_directory_def; dest_normal_def; is_some_def];
    REFL_TAC]);;

export_thm allocate_page_directory_h_dest_page_table;;

let allocate_page_directory_h_translate_page = prove
  (`!s s' ppa pd.
      wellformed s /\
      allocate_page_directory_h ppa s s' ==>
      translate_page s' pd =
      translate_page s (if pd = ppa then reference s else pd)`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`s : state`; `s' : state`; `ppa : physical_page_address`]
                 allocate_page_directory_h_dest_page_table) THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM MP_TAC THEN
   POP_ASSUM (K ALL_TAC) THEN
   REWRITE_TAC [allocate_page_directory_h_def] THEN
   DISCH_THEN (STRIP_ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
   POP_ASSUM (STRIP_ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
   STRIP_TAC THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   X_GEN_TAC `vpa : virtual_page_address` THEN
   REWRITE_TAC [translate_page_def] THEN
   POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
   ASM_REWRITE_TAC []);;

export_thm allocate_page_directory_h_translate_page;;

let allocate_page_directory_h_translate_page' = prove
  (`!s s' ppa pd.
      wellformed s /\
      allocate_page_directory_h ppa s s' ==>
      translate_page s pd =
      if pd = ppa then K NONE else translate_page s' pd`,
   REPEAT STRIP_TAC THEN
   COND_CASES_TAC THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC [FUN_EQ_THM] THEN
    X_GEN_TAC `vpa : virtual_page_address` THEN
    REWRITE_TAC [K_THM] THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC
      [allocate_page_directory_h_def; unmapped_normal_page_def;
       is_normal_page_def] THEN
    STRIP_TAC THEN
    POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM MP_TAC THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN
    REWRITE_TAC [translate_page_def] THEN
    page_cases_tac `status s ppa` THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC
      [is_page_directory_def; is_normal_def; is_some_def;
       dest_page_directory_def; dest_normal_def; case_option_def] THEN
    PAIR_CASES_TAC `dest_virtual_page_address vpa` THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [LET_DEF; LET_END_DEF];
    MATCH_MP_TAC EQ_SYM THEN
    MP_TAC (SPECL [`s : state`; `s' : state`; `ppa : physical_page_address`;
                   `pd : page_directory`]
                  allocate_page_directory_h_translate_page) THEN
    ASM_REWRITE_TAC []]);;

export_thm allocate_page_directory_h_translate_page';;

let allocate_page_directory_h_translate_page_cr3 = prove
  (`!s s' ppa.
      wellformed s /\
      allocate_page_directory_h ppa s s' ==>
      translate_page s (cr3 s) = translate_page s' (cr3 s')`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `ppa : physical_page_address`]
      allocate_page_directory_h_translate_page) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `ppa : physical_page_address`]
      allocate_page_directory_h_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [SYM th]) THEN
   MP_TAC (SPECL [`s : state`; `s' : state`; `ppa : physical_page_address`]
           allocate_page_directory_h_not_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

export_thm allocate_page_directory_h_translate_page_cr3;;

(* free_page_directory_h *)

let free_page_directory_h_cr3 = prove
  (`!s s' pd. free_page_directory_h pd s s' ==> cr3 s = cr3 s'`,
   REWRITE_TAC [free_page_directory_h_def] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC allocate_page_directory_h_cr3 THEN
   EXISTS_TAC `pd : physical_page_address` THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm free_page_directory_h_cr3;;

let free_page_directory_h_not_cr3 = prove
  (`!s s' pd.
      wellformed s' /\
      free_page_directory_h pd s s' ==>
      ~(cr3 s = pd)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [free_page_directory_h_def] THEN
   STRIP_TAC THEN
   MATCH_MP_TAC allocate_page_directory_h_not_cr3' THEN
   EXISTS_TAC `s' : state` THEN
   ASM_REWRITE_TAC []);;

export_thm free_page_directory_h_not_cr3;;

let free_page_directory_h_not_cr3' = prove
  (`!s s' pd.
      wellformed s' /\
      free_page_directory_h pd s s' ==>
      ~(cr3 s' = pd)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [free_page_directory_h_def] THEN
   STRIP_TAC THEN
   MATCH_MP_TAC allocate_page_directory_h_not_cr3 THEN
   EXISTS_TAC `s : state` THEN
   ASM_REWRITE_TAC []);;

export_thm free_page_directory_h_not_cr3';;

let free_page_directory_h_reference = prove
  (`!s s' pd.
      free_page_directory_h pd s s' ==> reference s = reference s'`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [free_page_directory_h_def] THEN
   STRIP_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC allocate_page_directory_h_reference THEN
   EXISTS_TAC `pd : physical_page_address` THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm free_page_directory_h_reference;;

let free_page_directory_h_regions = prove
  (`!s s' pd. free_page_directory_h pd s s' ==> regions s = regions s'`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [free_page_directory_h_def] THEN
   STRIP_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC allocate_page_directory_h_regions THEN
   EXISTS_TAC `pd : physical_page_address` THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm free_page_directory_h_regions;;

let free_page_directory_h_dest_environment = prove
  (`!s s' pd pt.
      wellformed s' /\
      free_page_directory_h pd s s' ==>
      dest_environment (status s' pt) = dest_environment (status s pt)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [free_page_directory_h_def] THEN
   STRIP_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC allocate_page_directory_h_dest_environment THEN
   EXISTS_TAC `pd : physical_page_address` THEN
   ASM_REWRITE_TAC []);;

export_thm free_page_directory_h_dest_environment;;

let free_page_directory_h_dest_page_table = prove
  (`!s s' pd pt.
      wellformed s' /\
      free_page_directory_h pd s s' ==>
      dest_page_table (status s' pt) = dest_page_table (status s pt)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [free_page_directory_h_def] THEN
   STRIP_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC allocate_page_directory_h_dest_page_table THEN
   EXISTS_TAC `pd : physical_page_address` THEN
   ASM_REWRITE_TAC []);;

export_thm free_page_directory_h_dest_page_table;;

let free_page_directory_h_translate_page = prove
  (`!s s' pd pd'.
      wellformed s' /\
      free_page_directory_h pd s s' ==>
      translate_page s' pd' =
      if pd' = pd then K NONE else translate_page s pd'`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [free_page_directory_h_def] THEN
   STRIP_TAC THEN
   MATCH_MP_TAC allocate_page_directory_h_translate_page' THEN
   ASM_REWRITE_TAC []);;

export_thm free_page_directory_h_translate_page;;

let free_page_directory_h_translate_page' = prove
  (`!s s' pd pd'.
      wellformed s' /\
      free_page_directory_h pd s s' ==>
      translate_page s pd' =
      translate_page s' (if pd' = pd then reference s' else pd')`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [free_page_directory_h_def] THEN
   STRIP_TAC THEN
   MATCH_MP_TAC allocate_page_directory_h_translate_page THEN
   ASM_REWRITE_TAC []);;

export_thm free_page_directory_h_translate_page';;

let free_page_directory_h_translate_page_cr3 = prove
  (`!s s' pd.
      wellformed s' /\
      free_page_directory_h pd s s' ==>
      translate_page s (cr3 s) = translate_page s' (cr3 s')`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [free_page_directory_h_def] THEN
   STRIP_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC allocate_page_directory_h_translate_page_cr3 THEN
   EXISTS_TAC `pd : physical_page_address` THEN
   ASM_REWRITE_TAC []);;

export_thm free_page_directory_h_translate_page_cr3;;

(* add_mapping *)

let add_mapping_cr3 = prove
  (`!s s' pd pts pr vr. add_mapping pd pts pr vr s s' ==> cr3 s = cr3 s'`,
   REWRITE_TAC [add_mapping_def] THEN
   REPEAT STRIP_TAC);;

export_thm add_mapping_cr3;;

let add_mapping_reference = prove
  (`!s s' pd pts pr vr.
      add_mapping pd pts pr vr s s' ==> reference s = reference s'`,
   REWRITE_TAC [add_mapping_def] THEN
   REPEAT STRIP_TAC);;

export_thm add_mapping_reference;;

let add_mapping_is_user_region = prove
  (`!s s' pd pts pr vr.
      add_mapping pd pts pr vr s s' ==> is_user_region vr`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [add_mapping_def] THEN
   STRIP_TAC);;

export_thm add_mapping_is_user_region;;

let add_mapping_status = prove
  (`!s s' pd pts pr vr ppa.
      add_mapping pd pts pr vr s s' /\
      ~(ppa = pd) /\
      ~(ppa IN pts) /\
      ~table_mapped_in_directory s pd ppa ==>
      status s ppa = status s' ppa`,
   REWRITE_TAC [add_mapping_def] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `ppa : physical_page_address`) THEN
   ASM_REWRITE_TAC []);;

export_thm add_mapping_status;;

let add_mapping_pd_was_page_directory = prove
  (`!s s' pd pts pr vr.
      add_mapping pd pts pr vr s s' ==>
      is_page_directory (status s pd)`,
   REWRITE_TAC [add_mapping_def] THEN
   REPEAT STRIP_TAC);;

export_thm add_mapping_pd_was_page_directory;;

let add_mapping_pts_were_unmapped_normal = prove
  (`!s s' pd pts pr vr pt.
      add_mapping pd pts pr vr s s' /\
      pt IN pts ==>
      unmapped_normal_page s pt`,
   REWRITE_TAC [add_mapping_def] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC []);;

export_thm add_mapping_pts_were_unmapped_normal;;

let add_mapping_pts_were_normal = prove
  (`!s s' pd pts pr vr pt.
      add_mapping pd pts pr vr s s' /\
      pt IN pts ==>
      is_normal_page s pt`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC unmapped_normal_page_normal THEN
   MATCH_MP_TAC add_mapping_pts_were_unmapped_normal THEN
   EXISTS_TAC `s' : state` THEN
   EXISTS_TAC `pd : page_directory` THEN
   EXISTS_TAC `pts : page_table set` THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC []);;

export_thm add_mapping_pts_were_normal;;

let add_mapping_pd_not_in_pts = prove
  (`!s s' pd pts pr vr.
      add_mapping pd pts pr vr s s' ==>
      ~(pd IN pts)`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN
     `is_page_directory (status s pd) /\
      is_normal (status s pd)` MP_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC add_mapping_pd_was_page_directory THEN
     EXISTS_TAC `s' : state` THEN
     EXISTS_TAC `pts : page_table set` THEN
     EXISTS_TAC `pr : physical_region` THEN
     EXISTS_TAC `vr : virtual_region` THEN
     ASM_REWRITE_TAC [];
     REWRITE_TAC [GSYM is_normal_page_def] THEN
     MATCH_MP_TAC add_mapping_pts_were_normal THEN
     EXISTS_TAC `s' : state` THEN
     EXISTS_TAC `pd : page_directory` THEN
     EXISTS_TAC `pts : page_table set` THEN
     EXISTS_TAC `pr : physical_region` THEN
     EXISTS_TAC `vr : virtual_region` THEN
     ASM_REWRITE_TAC []];
    page_cases_tac `status s pd` THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC
      [is_normal_def; dest_normal_def; is_some_def; is_page_directory_def;
       dest_page_directory_def]]);;

export_thm add_mapping_pd_not_in_pts;;

let add_mapping_pd_is_page_directory = prove
  (`!s s' pd pts pr vr.
      add_mapping pd pts pr vr s s' ==>
      is_page_directory (status s' pd)`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `~((pd : page_directory) IN pts)` MP_TAC THENL
   [MATCH_MP_TAC add_mapping_pd_not_in_pts THEN
    EXISTS_TAC `s : state` THEN
    EXISTS_TAC `s' : state` THEN
    EXISTS_TAC `pr : physical_region` THEN
    EXISTS_TAC `vr : virtual_region` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [add_mapping_def]) THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `pd : page_directory`) THEN
   ASM_REWRITE_TAC []);;

export_thm add_mapping_pd_is_page_directory;;

let add_mapping_pts_mapped_in_pd = prove
  (`!s s' pd pts pr vr pt.
      add_mapping pd pts pr vr s s' /\
      pt IN pts ==>
      table_mapped_in_directory s' pd pt`,
   REWRITE_TAC [add_mapping_def] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `pt : page_table`) THEN
   ASM_REWRITE_TAC []);;

export_thm add_mapping_pts_mapped_in_pd;;

let add_mapping_pts_are_page_tables = prove
  (`!s s' pd pts pr vr pt.
      wellformed s' /\
      add_mapping pd pts pr vr s s' /\
      pt IN pts ==>
      is_page_table (status s' pt)`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC table_mapped_in_directory_is_page_table THEN
   EXISTS_TAC `pd : page_directory` THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC add_mapping_pts_mapped_in_pd THEN
   EXISTS_TAC `s : state` THEN
   EXISTS_TAC `pts : page_table set` THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC []);;

export_thm add_mapping_pts_are_page_tables;;

let add_mapping_is_page_table = prove
  (`!s s' pd pts pr vr ppa.
      wellformed s /\
      add_mapping pd pts pr vr s s' /\
      ~(ppa IN pts) ==>
      is_page_table (status s ppa) = is_page_table (status s' ppa)`,
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `ppa = (pd : page_directory)` THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `F` THEN
    REWRITE_TAC [] THEN
    CONJ_TAC THENL
    [MP_TAC
       (SPECL
          [`s : state`;
           `s' : state`;
           `pd : page_directory`;
           `pts : page_table set`;
           `pr : physical_region`;
           `vr : virtual_region`]
          add_mapping_pd_was_page_directory) THEN
     ASM_REWRITE_TAC [] THEN
     page_cases_tac `status s pd` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [is_page_table_def; dest_page_table_def;
        is_page_directory_def; dest_page_directory_def;
        is_some_def];
     MP_TAC
       (SPECL
          [`s : state`;
           `s' : state`;
           `pd : page_directory`;
           `pts : page_table set`;
           `pr : physical_region`;
           `vr : virtual_region`]
          add_mapping_pd_is_page_directory) THEN
     ASM_REWRITE_TAC [] THEN
     page_cases_tac `status s' pd` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [is_page_table_def; dest_page_table_def;
        is_page_directory_def; dest_page_directory_def;
        is_some_def]];
    ALL_TAC] THEN
   ASM_CASES_TAC `table_mapped_in_directory s pd ppa` THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `T` THEN
    REWRITE_TAC [] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC table_mapped_in_directory_is_page_table THEN
     EXISTS_TAC `pd : page_directory` THEN
     ASM_REWRITE_TAC [];
     UNDISCH_TAC `add_mapping pd pts pr vr s s'` THEN
     REWRITE_TAC [add_mapping_def] THEN
     STRIP_TAC THEN
     FIRST_X_ASSUM (MP_TAC o SPEC `ppa : physical_page_address`) THEN
     ASM_REWRITE_TAC []];
    ALL_TAC] THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC add_mapping_status THEN
   EXISTS_TAC `pd : page_directory` THEN
   EXISTS_TAC `pts : page_table set` THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC []);;

export_thm add_mapping_is_page_table;;

let add_mapping_dest_environment = prove
  (`!s s' pd pts pr vr ppa.
      wellformed s /\
      wellformed s' /\
      add_mapping pd pts pr vr s s' ==>
      dest_environment (status s ppa) = dest_environment (status s' ppa)`,
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `ppa = (pd : page_directory)` THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `NONE : page_data option` THEN
    CONJ_TAC THENL
    [MP_TAC
       (SPECL
          [`s : state`;
           `s' : state`;
           `pd : page_directory`;
           `pts : page_table set`;
           `pr : physical_region`;
           `vr : virtual_region`]
          add_mapping_pd_was_page_directory) THEN
     ASM_REWRITE_TAC [] THEN
     page_cases_tac `status s pd` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [is_environment_def; dest_environment_def;
        is_normal_def; dest_normal_def;
        is_page_table_def; dest_page_table_def;
        is_page_directory_def; dest_page_directory_def;
        is_some_def; option_distinct; option_inj];
     MP_TAC
       (SPECL
          [`s : state`;
           `s' : state`;
           `pd : page_directory`;
           `pts : page_table set`;
           `pr : physical_region`;
           `vr : virtual_region`]
          add_mapping_pd_is_page_directory) THEN
     ASM_REWRITE_TAC [] THEN
     page_cases_tac `status s' pd` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [is_environment_def; dest_environment_def;
        is_normal_def; dest_normal_def;
        is_page_table_def; dest_page_table_def;
        is_page_directory_def; dest_page_directory_def;
        is_some_def; option_distinct; option_inj]];
    ALL_TAC] THEN
   ASM_CASES_TAC `(ppa : physical_page_address) IN pts` THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `NONE : page_data option` THEN
    CONJ_TAC THENL
    [MP_TAC
       (SPECL
          [`s : state`;
           `s' : state`;
           `pd : page_directory`;
           `pts : page_table set`;
           `pr : physical_region`;
           `vr : virtual_region`;
           `ppa : physical_page_address`]
          add_mapping_pts_were_normal) THEN
     ASM_REWRITE_TAC [is_normal_page_def] THEN
     page_cases_tac `status s ppa` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [is_environment_def; dest_environment_def;
        is_normal_def; dest_normal_def;
        is_page_table_def; dest_page_table_def;
        is_page_directory_def; dest_page_directory_def;
        is_some_def; option_distinct; option_inj];
     MP_TAC
       (SPECL
          [`s : state`;
           `s' : state`;
           `pd : page_directory`;
           `pts : page_table set`;
           `pr : physical_region`;
           `vr : virtual_region`;
           `ppa : physical_page_address`]
          add_mapping_pts_are_page_tables) THEN
     ASM_REWRITE_TAC [] THEN
     page_cases_tac `status s' ppa` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [is_environment_def; dest_environment_def;
        is_normal_def; dest_normal_def;
        is_page_table_def; dest_page_table_def;
        is_page_directory_def; dest_page_directory_def;
        is_some_def; option_distinct; option_inj]];
    ALL_TAC] THEN
   ASM_CASES_TAC `table_mapped_in_directory s pd ppa` THENL
   [SUBGOAL_THEN `is_page_table (status s ppa)` ASSUME_TAC THENL
    [MATCH_MP_TAC table_mapped_in_directory_is_page_table THEN
     EXISTS_TAC `pd : page_directory` THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `NONE : page_data option` THEN
    CONJ_TAC THENL
    [POP_ASSUM MP_TAC THEN
     page_cases_tac `status s ppa` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [is_environment_def; dest_environment_def;
        is_normal_def; dest_normal_def;
        is_page_table_def; dest_page_table_def;
        is_page_directory_def; dest_page_directory_def;
        is_some_def; option_distinct; option_inj];
     MP_TAC
       (SPECL
          [`s : state`;
           `s' : state`;
           `pd : page_directory`;
           `pts : page_table set`;
           `pr : physical_region`;
           `vr : virtual_region`;
           `ppa : physical_page_address`]
          add_mapping_is_page_table) THEN
       ASM_REWRITE_TAC [] THEN
     page_cases_tac `status s' ppa` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [is_environment_def; dest_environment_def;
        is_normal_def; dest_normal_def;
        is_page_table_def; dest_page_table_def;
        is_page_directory_def; dest_page_directory_def;
        is_some_def; option_distinct; option_inj]];
    ALL_TAC] THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC add_mapping_status THEN
   EXISTS_TAC `pd : page_directory` THEN
   EXISTS_TAC `pts : page_table set` THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC []);;

export_thm add_mapping_dest_environment;;

let add_mapping_is_environment = prove
  (`!s s' pd pts pr vr ppa.
      wellformed s /\
      wellformed s' /\
      add_mapping pd pts pr vr s s' ==>
      is_environment (status s ppa) = is_environment (status s' ppa)`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [is_environment_def] THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC add_mapping_dest_environment THEN
   EXISTS_TAC `pd : page_directory` THEN
   EXISTS_TAC `pts : page_table set` THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC []);;

export_thm add_mapping_is_environment;;

let add_mapping_is_page_directory = prove
  (`!s s' pd pts pr vr ppa.
      wellformed s /\
      wellformed s' /\
      add_mapping pd pts pr vr s s' ==>
      is_page_directory (status s ppa) = is_page_directory (status s' ppa)`,
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `ppa = (pd : page_directory)` THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `T` THEN
    REWRITE_TAC [] THEN
    CONJ_TAC THENL
    [MP_TAC
       (SPECL
          [`s : state`;
           `s' : state`;
           `pd : page_directory`;
           `pts : page_table set`;
           `pr : physical_region`;
           `vr : virtual_region`]
          add_mapping_pd_was_page_directory) THEN
     ASM_REWRITE_TAC [];
     MP_TAC
       (SPECL
          [`s : state`;
           `s' : state`;
           `pd : page_directory`;
           `pts : page_table set`;
           `pr : physical_region`;
           `vr : virtual_region`]
          add_mapping_pd_is_page_directory) THEN
     ASM_REWRITE_TAC []];
    ALL_TAC] THEN
   ASM_CASES_TAC `(ppa : physical_page_address) IN pts` THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `F` THEN
    REWRITE_TAC [] THEN
    CONJ_TAC THENL
    [MP_TAC
       (SPECL
          [`s : state`;
           `s' : state`;
           `pd : page_directory`;
           `pts : page_table set`;
           `pr : physical_region`;
           `vr : virtual_region`;
           `ppa : physical_page_address`]
          add_mapping_pts_were_normal) THEN
     ASM_REWRITE_TAC [is_normal_page_def] THEN
     page_cases_tac `status s ppa` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [is_normal_def; dest_normal_def;
        is_page_directory_def; dest_page_directory_def;
        is_some_def];
     MP_TAC
       (SPECL
          [`s : state`;
           `s' : state`;
           `pd : page_directory`;
           `pts : page_table set`;
           `pr : physical_region`;
           `vr : virtual_region`;
           `ppa : physical_page_address`]
          add_mapping_pts_are_page_tables) THEN
     ASM_REWRITE_TAC [] THEN
     page_cases_tac `status s' ppa` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [is_page_table_def; dest_page_table_def;
        is_page_directory_def; dest_page_directory_def;
        is_some_def]];
    ALL_TAC] THEN
   ASM_CASES_TAC `table_mapped_in_directory s pd ppa` THENL
   [SUBGOAL_THEN `is_page_table (status s ppa)` ASSUME_TAC THENL
    [MATCH_MP_TAC table_mapped_in_directory_is_page_table THEN
     EXISTS_TAC `pd : page_directory` THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `F` THEN
    REWRITE_TAC [] THEN
    CONJ_TAC THENL
    [POP_ASSUM MP_TAC THEN
     page_cases_tac `status s ppa` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [is_page_table_def; dest_page_table_def;
        is_page_directory_def; dest_page_directory_def;
        is_some_def];
     POP_ASSUM MP_TAC THEN
     MP_TAC
       (SPECL
          [`s : state`;
           `s' : state`;
           `pd : page_directory`;
           `pts : page_table set`;
           `pr : physical_region`;
           `vr : virtual_region`;
           `ppa : physical_page_address`]
          add_mapping_is_page_table) THEN
       ASM_REWRITE_TAC [] THEN
       DISCH_THEN SUBST1_TAC THEN
       page_cases_tac `status s' ppa` THEN
       STRIP_TAC THEN
       ASM_REWRITE_TAC
         [is_page_table_def; dest_page_table_def;
          is_page_directory_def; dest_page_directory_def;
          is_some_def]];
    ALL_TAC] THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC add_mapping_status THEN
   EXISTS_TAC `pd : page_directory` THEN
   EXISTS_TAC `pts : page_table set` THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC []);;

export_thm add_mapping_is_page_directory;;

let add_mapping_dest_page_directory = prove
  (`!s s' pd pts pr vr ppa.
      wellformed s /\
      wellformed s' /\
      add_mapping pd pts pr vr s s' /\
      ~(ppa = pd) ==>
      dest_page_directory (status s ppa) = dest_page_directory (status s' ppa)`,
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `is_page_directory (status s ppa)` THENL
   [AP_TERM_TAC THEN
    MATCH_MP_TAC add_mapping_status THEN
    EXISTS_TAC `pd : page_directory` THEN
    EXISTS_TAC `pts : page_table set` THEN
    EXISTS_TAC `pr : physical_region` THEN
    EXISTS_TAC `vr : virtual_region` THEN
    ASM_REWRITE_TAC [] THEN
    REPEAT STRIP_TAC THENL
    [MP_TAC
       (SPECL
          [`s : state`;
           `s' : state`;
           `pd : page_directory`;
           `pts : page_table set`;
           `pr : physical_region`;
           `vr : virtual_region`;
           `ppa : physical_page_address`]
          add_mapping_pts_were_normal) THEN
     ASM_REWRITE_TAC [is_normal_page_def] THEN
     UNDISCH_TAC `is_page_directory (status s ppa)` THEN
     page_cases_tac `status s ppa` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [is_normal_def; dest_normal_def;
        is_page_directory_def; dest_page_directory_def;
        is_some_def];
     MP_TAC
       (SPECL
          [`s : state`;
           `pd : page_directory`;
           `ppa : physical_page_address`]
          table_mapped_in_directory_is_page_table) THEN
     ASM_REWRITE_TAC [] THEN
     UNDISCH_TAC `is_page_directory (status s ppa)` THEN
     page_cases_tac `status s ppa` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [is_page_table_def; dest_page_table_def;
        is_page_directory_def; dest_page_directory_def;
        is_some_def]];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `NONE : page_directory_data option` THEN
    CONJ_TAC THENL
    [POP_ASSUM MP_TAC THEN
     REWRITE_TAC [is_page_directory_def] THEN
     option_cases_tac `dest_page_directory (status s ppa)` THENL
     [DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [];
      DISCH_THEN (X_CHOOSE_THEN `pdd : page_directory_data` SUBST1_TAC) THEN
      REWRITE_TAC [is_some_def]];
     POP_ASSUM MP_TAC THEN
     MP_TAC
       (SPECL
          [`s : state`;
           `s' : state`;
           `pd : page_directory`;
           `pts : page_table set`;
           `pr : physical_region`;
           `vr : virtual_region`;
           `ppa : physical_page_address`]
          add_mapping_is_page_directory) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC [is_page_directory_def] THEN
     option_cases_tac `dest_page_directory (status s' ppa)` THENL
     [DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [];
      DISCH_THEN (X_CHOOSE_THEN `pdd : page_directory_data` SUBST1_TAC) THEN
      REWRITE_TAC [is_some_def]]]]);;

export_thm add_mapping_dest_page_directory;;

let add_mapping_dest_page_table = prove
  (`!s s' pd pts pr vr ppa.
      add_mapping pd pts pr vr s s' /\
      ~(ppa IN pts) /\
      ~table_mapped_in_directory s pd ppa ==>
      dest_page_table (status s ppa) = dest_page_table (status s' ppa)`,
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `ppa = (pd : page_directory)` THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `NONE : page_table_data option` THEN
    CONJ_TAC THENL
    [MP_TAC
       (SPECL
          [`s : state`;
           `s' : state`;
           `pd : page_directory`;
           `pts : page_table set`;
           `pr : physical_region`;
           `vr : virtual_region`]
          add_mapping_pd_was_page_directory) THEN
     ASM_REWRITE_TAC [] THEN
     page_cases_tac `status s pd` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [is_page_table_def; dest_page_table_def;
        is_page_directory_def; dest_page_directory_def;
        is_some_def];
     MP_TAC
       (SPECL
          [`s : state`;
           `s' : state`;
           `pd : page_directory`;
           `pts : page_table set`;
           `pr : physical_region`;
           `vr : virtual_region`]
          add_mapping_pd_is_page_directory) THEN
     ASM_REWRITE_TAC [] THEN
     page_cases_tac `status s' pd` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [is_page_table_def; dest_page_table_def;
        is_page_directory_def; dest_page_directory_def;
        is_some_def]];
    ALL_TAC] THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC add_mapping_status THEN
   EXISTS_TAC `pd : page_directory` THEN
   EXISTS_TAC `pts : page_table set` THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC []);;

export_thm add_mapping_dest_page_table;;

let add_mapping_translate_page_pd = prove
  (`!s s' pd pts pr vr vpa.
      add_mapping pd pts pr vr s s' /\
      ~member_virtual_region vpa vr ==>
      translate_page s pd vpa = translate_page s' pd vpa`,
   REWRITE_TAC [add_mapping_def] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `vpa : virtual_page_address`) THEN
   ASM_REWRITE_TAC []);;

export_thm add_mapping_translate_page_pd;;

let add_mapping_translate_page_reference = prove
  (`!s s' pd pts pr vr.
      wellformed s /\
      wellformed s' /\
      add_mapping pd pts pr vr s s' ==>
      translate_page s (reference s) = translate_page s' (reference s')`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   X_GEN_TAC `vpa : virtual_page_address` THEN
   ASM_CASES_TAC `is_kernel_page_address vpa` THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `translate_page s pd vpa` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC EQ_SYM THEN
     MATCH_MP_TAC page_directories_contain_reference THEN
     ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC add_mapping_pd_was_page_directory THEN
     EXISTS_TAC `s' : state` THEN
     EXISTS_TAC `pts : page_table set` THEN
     EXISTS_TAC `pr : physical_region` THEN
     EXISTS_TAC `vr : virtual_region` THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `translate_page s' pd vpa` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC add_mapping_translate_page_pd THEN
     EXISTS_TAC `pts : page_table set` THEN
     EXISTS_TAC `pr : physical_region` THEN
     EXISTS_TAC `vr : virtual_region` THEN
     ASM_REWRITE_TAC [] THEN
     STRIP_TAC THEN
     UNDISCH_TAC `is_kernel_page_address vpa` THEN
     REWRITE_TAC [GSYM is_user_page_address_def] THEN
     MATCH_MP_TAC is_user_region THEN
     EXISTS_TAC `vr : virtual_region` THEN
     ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC add_mapping_is_user_region THEN
     EXISTS_TAC `s : state` THEN
     EXISTS_TAC `s' : state` THEN
     EXISTS_TAC `pd : page_directory` THEN
     EXISTS_TAC `pts : page_table set` THEN
     EXISTS_TAC `pr : physical_region` THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    MATCH_MP_TAC page_directories_contain_reference THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC add_mapping_pd_is_page_directory THEN
    EXISTS_TAC `s : state` THEN
    EXISTS_TAC `pts : page_table set` THEN
    EXISTS_TAC `pr : physical_region` THEN
    EXISTS_TAC `vr : virtual_region` THEN
    ASM_REWRITE_TAC [];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `NONE : physical_page_address option` THEN
    CONJ_TAC THENL
    [MP_TAC
       (SPECL
         [`s : state`;
          `vpa : virtual_page_address`]
         reference_maps_kernel_addresses) THEN
     ASM_REWRITE_TAC [mapped_page_def] THEN
     option_cases_tac `translate_page s (reference s) vpa` THENL
     [DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [];
      STRIP_TAC THEN
      ASM_REWRITE_TAC [is_some_def]];
     MP_TAC
       (SPECL
         [`s' : state`;
          `vpa : virtual_page_address`]
         reference_maps_kernel_addresses) THEN
     ASM_REWRITE_TAC [mapped_page_def] THEN
     option_cases_tac `translate_page s' (reference s') vpa` THENL
     [DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [];
      STRIP_TAC THEN
      ASM_REWRITE_TAC [is_some_def]]]]);;

export_thm add_mapping_translate_page_reference;;

let add_mapping_translate_kernel_page = prove
  (`!s s' pd pts pr vr pd' vpa.
      wellformed s /\
      wellformed s' /\
      add_mapping pd pts pr vr s s' /\
      is_kernel_page_address vpa ==>
      translate_page s pd' vpa = translate_page s' pd' vpa`,
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `is_page_directory (status s pd')` THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `translate_page s (reference s) vpa` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC page_directories_contain_reference THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `translate_page s' (reference s') vpa` THEN
    CONJ_TAC THENL
    [AP_THM_TAC THEN
     MATCH_MP_TAC add_mapping_translate_page_reference THEN
     EXISTS_TAC `pd : page_directory` THEN
     EXISTS_TAC `pts : page_table set` THEN
     EXISTS_TAC `pr : physical_region` THEN
     EXISTS_TAC `vr : virtual_region` THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC page_directories_contain_reference THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC
      (SPECL
         [`s : state`;
          `s' : state`;
          `pd : page_directory`;
          `pts : page_table set`;
          `pr : physical_region`;
          `vr : virtual_region`;
          `pd' : page_directory`]
         add_mapping_is_page_directory) THEN
    ASM_REWRITE_TAC [];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `NONE : physical_page_address option` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC translate_page_is_not_page_directory THEN
     ASM_REWRITE_TAC [];
     MATCH_MP_TAC EQ_SYM THEN
     MATCH_MP_TAC translate_page_is_not_page_directory THEN
     POP_ASSUM MP_TAC THEN
     MATCH_MP_TAC EQ_IMP THEN
     AP_TERM_TAC THEN
     MATCH_MP_TAC add_mapping_is_page_directory THEN
     EXISTS_TAC `pd : page_directory` THEN
     EXISTS_TAC `pts : page_table set` THEN
     EXISTS_TAC `pr : physical_region` THEN
     EXISTS_TAC `vr : virtual_region` THEN
     ASM_REWRITE_TAC []]]);;

export_thm add_mapping_translate_kernel_page;;

let add_mapping_translate_page = prove
  (`!s s' pd pts pr vr pd'.
      wellformed s /\
      wellformed s' /\
      add_mapping pd pts pr vr s s' /\
      ~(pd' = pd) ==>
      translate_page s pd' = translate_page s' pd'`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   X_GEN_TAC `vpa : virtual_page_address` THEN
   ASM_CASES_TAC `is_kernel_page_address vpa` THENL
   [MATCH_MP_TAC add_mapping_translate_kernel_page THEN
    EXISTS_TAC `pd : page_directory` THEN
    EXISTS_TAC `pts : page_table set` THEN
    EXISTS_TAC `pr : physical_region` THEN
    EXISTS_TAC `vr : virtual_region` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   REWRITE_TAC [translate_page_def] THEN
   MP_TAC
     (SPECL
        [`s : state`;
         `s' : state`;
         `pd : page_directory`;
         `pts : page_table set`;
         `pr : physical_region`;
         `vr : virtual_region`;
         `pd' : physical_page_address`]
        add_mapping_dest_page_directory) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   option_cases_tac `dest_page_directory (status s pd')` THENL
   [DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [case_option_def];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `pdd : page_directory_data` ASSUME_TAC) THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   virtual_page_address_cases_tac `vpa : virtual_page_address` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [virtual_page_address_tybij] THEN
   REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
   option_cases_tac `dest_page_directory_data pdd vsa` THENL
   [DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [case_option_def];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `pde : page_directory_entry` ASSUME_TAC) THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   page_directory_entry_cases_tac `pde : page_directory_entry` THENL
   [STRIP_TAC THEN
    ASM_REWRITE_TAC [case_page_directory_entry_def];
    ALL_TAC] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_page_directory_entry_def] THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC add_mapping_dest_page_table THEN
   EXISTS_TAC `pd : page_directory` THEN
   EXISTS_TAC `pts : page_table set` THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THENL
   [MP_TAC
      (SPECL
         [`s : state`;
          `s' : state`;
          `pd : page_directory`;
          `pts : page_table set`;
          `pr : physical_region`;
          `vr : virtual_region`;
          `pt : page_table`]
         add_mapping_pts_were_normal) THEN
    ASM_REWRITE_TAC [is_normal_page_def] THEN
    MP_TAC
      (SPECL
         [`s : state`;
          `pd' : page_directory`;
          `pdd : page_directory_data`;
          `vsa : virtual_superpage_address`;
          `pt : page_table`]
         table_pointers_are_page_tables) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [] THEN
     UNDISCH_TAC `dest_page_directory (status s pd') = SOME pdd` THEN
     page_cases_tac `status s pd'` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [is_page_table_def; dest_page_table_def;
        is_page_directory_def; dest_page_directory_def;
        is_some_def; option_distinct; option_inj] THEN
     DISCH_THEN SUBST1_TAC THEN
     REFL_TAC;
     ALL_TAC] THEN
    page_cases_tac `status s pt` THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC
      [is_environment_def; dest_environment_def;
       is_normal_def; dest_normal_def;
       is_page_table_def; dest_page_table_def;
       is_page_directory_def; dest_page_directory_def;
       is_some_def; option_distinct; option_inj];
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [table_mapped_in_directory] THEN
    STRIP_TAC THEN
    MP_TAC
      (SPECL
         [`s : state`;
          `pt : page_table`;
          `pd' : page_directory`;
          `pd : page_directory`;
          `pdd : page_directory_data`;
          `pdd' : page_directory_data`;
          `vsa : virtual_superpage_address`;
          `pdi : virtual_superpage_address`]
         no_shared_page_tables) THEN
    ASM_REWRITE_TAC [dest_page_directory_def] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM (SUBST_VAR_TAC o SYM) THEN
    UNDISCH_TAC `~is_kernel_page_address vpa` THEN
    ASM_REWRITE_TAC
      [is_kernel_page_address_def; virtual_page_address_tybij;
       LET_DEF; LET_END_DEF]]);;

export_thm add_mapping_translate_page;;

let add_mapping_translate_kernel_page_cr3 = prove
  (`!s s' pd pts pr vr vpa.
      wellformed s /\
      wellformed s' /\
      add_mapping pd pts pr vr s s' /\
      is_kernel_page_address vpa ==>
      translate_page s (cr3 s) vpa = translate_page s' (cr3 s') vpa`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`s : state`;
         `s' : state`;
         `pd : page_directory`;
         `pts : page_table set`;
         `pr : physical_region`;
         `vr : virtual_region`]
        add_mapping_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC add_mapping_translate_kernel_page THEN
   EXISTS_TAC `pd : page_directory` THEN
   EXISTS_TAC `pts : page_table set` THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC []);;

export_thm add_mapping_translate_kernel_page_cr3;;

(* add_mapping_h *)

let add_mapping_h_cr3 = prove
  (`!s s' pd pts pr vr. add_mapping_h pd pts pr vr s s' ==> cr3 s = cr3 s'`,
   REWRITE_TAC [add_mapping_h_def] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC add_mapping_cr3 THEN
   EXISTS_TAC `pd : page_directory` THEN
   EXISTS_TAC `set_of_list (take n (pts : page_table list))` THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm add_mapping_h_cr3;;

let add_mapping_h_dest_environment = prove
  (`!s s' pd pts pr vr ppa.
      wellformed s /\
      wellformed s' /\
      add_mapping_h pd pts pr vr s s' ==>
      dest_environment (status s ppa) = dest_environment (status s' ppa)`,
   REWRITE_TAC [add_mapping_h_def] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC add_mapping_dest_environment THEN
   EXISTS_TAC `pd : page_directory` THEN
   EXISTS_TAC `set_of_list (take n (pts : page_table list))` THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC []);;

export_thm add_mapping_h_dest_environment;;

let add_mapping_h_is_environment = prove
  (`!s s' pd pts pr vr ppa.
      wellformed s /\
      wellformed s' /\
      add_mapping_h pd pts pr vr s s' ==>
      is_environment (status s ppa) = is_environment (status s' ppa)`,
   REWRITE_TAC [add_mapping_h_def] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC add_mapping_is_environment THEN
   EXISTS_TAC `pd : page_directory` THEN
   EXISTS_TAC `set_of_list (take n (pts : page_table list))` THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC []);;

export_thm add_mapping_h_is_environment;;

let add_mapping_h_translate_kernel_page = prove
  (`!s s' pd pts pr vr pd' vpa.
      wellformed s /\
      wellformed s' /\
      add_mapping_h pd pts pr vr s s' /\
      is_kernel_page_address vpa ==>
      translate_page s pd' vpa = translate_page s' pd' vpa`,
   REWRITE_TAC [add_mapping_h_def] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC add_mapping_translate_kernel_page THEN
   EXISTS_TAC `pd : page_directory` THEN
   EXISTS_TAC `set_of_list (take n (pts : page_table list))` THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC []);;

export_thm add_mapping_h_translate_kernel_page;;

let add_mapping_h_translate_kernel_page_cr3 = prove
  (`!s s' pd pts pr vr vpa.
      wellformed s /\
      wellformed s' /\
      add_mapping_h pd pts pr vr s s' /\
      is_kernel_page_address vpa ==>
      translate_page s (cr3 s) vpa = translate_page s' (cr3 s') vpa`,
   REWRITE_TAC [add_mapping_h_def] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC add_mapping_translate_kernel_page_cr3 THEN
   EXISTS_TAC `pd : page_directory` THEN
   EXISTS_TAC `set_of_list (take n (pts : page_table list))` THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC []);;

export_thm add_mapping_h_translate_kernel_page_cr3;;

(* remove_mapping_h *)

let remove_mapping_h = prove
  (`!s s' pd vr.
      remove_mapping_h pd vr s s' <=>
      ?prs pr pts.
        translate_page s pd (virtual_region_start vr) = SOME prs /\
        PhysicalRegion prs (virtual_region_length vr) = pr /\
        { ppa | is_page_table (status s ppa) /\
                status s' ppa = Normal zero_page_data } = pts /\
        add_mapping pd pts pr vr s' s`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [remove_mapping_h_def] THEN
   option_cases_tac `translate_page s pd (virtual_region_start vr)` THENL
   [STRIP_TAC THEN
    ASM_REWRITE_TAC [case_option_def; option_distinct];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `prs : physical_page_address` ASSUME_TAC) THEN
   ASM_REWRITE_TAC
     [case_option_def; option_inj; GSYM RIGHT_AND_EXISTS_THM; UNWIND_THM1;
      LET_DEF; LET_END_DEF]);;

export_thm remove_mapping_h;;

let remove_mapping_h_was_mapped = prove
  (`!s s' pd vr.
      remove_mapping_h pd vr s s' ==>
      ?ppa. translate_page s pd (virtual_region_start vr) = SOME ppa`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [remove_mapping_h] THEN
   STRIP_TAC THEN
   EXISTS_TAC `prs : physical_page_address` THEN
   ASM_REWRITE_TAC []);;

export_thm remove_mapping_h_was_mapped;;

let remove_mapping_h_cr3 = prove
  (`!s s' pd vr. remove_mapping_h pd vr s s' ==> cr3 s = cr3 s'`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [remove_mapping_h] THEN
   STRIP_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC add_mapping_cr3 THEN
   EXISTS_TAC `pd : page_directory` THEN
   EXISTS_TAC `pts : page_table set` THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm remove_mapping_h_cr3;;

let remove_mapping_h_dest_environment = prove
  (`!s s' pd vr ppa.
      wellformed s /\
      wellformed s' /\
      remove_mapping_h pd vr s s' ==>
      dest_environment (status s ppa) = dest_environment (status s' ppa)`,
   REWRITE_TAC [remove_mapping_h] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC add_mapping_dest_environment THEN
   EXISTS_TAC `pd : page_directory` THEN
   EXISTS_TAC `pts : page_table set` THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC []);;

export_thm remove_mapping_h_dest_environment;;

let remove_mapping_h_is_environment = prove
  (`!s s' pd vr ppa.
      wellformed s /\
      wellformed s' /\
      remove_mapping_h pd vr s s' ==>
      is_environment (status s ppa) = is_environment (status s' ppa)`,
   REWRITE_TAC [remove_mapping_h] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC add_mapping_is_environment THEN
   EXISTS_TAC `pd : page_directory` THEN
   EXISTS_TAC `pts : page_table set` THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC []);;

export_thm remove_mapping_h_is_environment;;

let remove_mapping_h_translate_kernel_page = prove
  (`!s s' pd vr pd' vpa.
      wellformed s /\
      wellformed s' /\
      remove_mapping_h pd vr s s' /\
      is_kernel_page_address vpa ==>
      translate_page s pd' vpa = translate_page s' pd' vpa`,
   REWRITE_TAC [remove_mapping_h] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC add_mapping_translate_kernel_page THEN
   EXISTS_TAC `pd : page_directory` THEN
   EXISTS_TAC `pts : page_table set` THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC []);;

export_thm remove_mapping_h_translate_kernel_page;;

let remove_mapping_h_translate_kernel_page_cr3 = prove
  (`!s s' pd vr vpa.
      wellformed s /\
      wellformed s' /\
      remove_mapping_h pd vr s s' /\
      is_kernel_page_address vpa ==>
      translate_page s (cr3 s) vpa = translate_page s' (cr3 s') vpa`,
   REWRITE_TAC [remove_mapping_h] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC add_mapping_translate_kernel_page_cr3 THEN
   EXISTS_TAC `pd : page_directory` THEN
   EXISTS_TAC `pts : page_table set` THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC []);;

export_thm remove_mapping_h_translate_kernel_page_cr3;;

(* add_kernel_mapping_h *)

let add_kernel_mapping_h_cr3 = prove
  (`!s s' pr vr. add_kernel_mapping_h pr vr s s' ==> cr3 s = cr3 s'`,
   REWRITE_TAC [add_kernel_mapping_h_def] THEN
   REPEAT STRIP_TAC);;

export_thm add_kernel_mapping_h_cr3;;

let add_kernel_mapping_h_reference = prove
  (`!s s' pr vr. add_kernel_mapping_h pr vr s s' ==> reference s = reference s'`,
   REWRITE_TAC [add_kernel_mapping_h_def] THEN
   REPEAT STRIP_TAC);;

export_thm add_kernel_mapping_h_reference;;

let add_kernel_mapping_h_is_kernel_region = prove
  (`!s s' pr vr.
      add_kernel_mapping_h pr vr s s' ==>
      is_kernel_region vr`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [add_kernel_mapping_h_def] THEN
   STRIP_TAC);;

export_thm add_kernel_mapping_h_is_kernel_region;;

let add_kernel_mapping_h_mapped_is_normal_page = prove
  (`!s s' pr vr ppa.
      add_kernel_mapping_h pr vr s s' /\
      member_physical_region ppa pr ==>
      is_normal_page s ppa`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [add_kernel_mapping_h_def] THEN
   STRIP_TAC THEN
   POP_ASSUM MP_TAC THEN
   UNDISCH_TAC `forall_physical_region (is_normal_page s) pr` THEN
   POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC
     [forall_physical_region_def; member_physical_region_def;
      GSYM ALL_MEM] THEN
   DISCH_THEN MATCH_ACCEPT_TAC);;

export_thm add_kernel_mapping_h_mapped_is_normal_page;;

let add_kernel_mapping_h_mapped_wasnt_environment = prove
  (`!s s' pr vr vpa ppa.
      add_kernel_mapping_h pr vr s s' /\
      member_virtual_region vpa vr /\
      translate_page s (reference s) vpa = SOME ppa ==>
      ~is_environment_page s ppa`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [add_kernel_mapping_h_def; member_virtual_region_def] THEN
   STRIP_TAC THEN
   UNDISCH_TAC
     `forall_virtual_region
        (\vpa. case_option T (\ppa. ~is_environment_page s ppa)
               (translate_page s (reference s) vpa)) vr` THEN
   REWRITE_TAC [forall_virtual_region_def; GSYM ALL_MEM] THEN
   DISCH_THEN (MP_TAC o SPEC `vpa : virtual_page_address`) THEN
   ASM_REWRITE_TAC [case_option_def]);;

export_thm add_kernel_mapping_h_mapped_wasnt_environment;;

let add_kernel_mapping_h_status = prove
  (`!s s' pr vr ppa.
      add_kernel_mapping_h pr vr s s' /\
      ~table_mapped_in_directory s (reference s) ppa ==>
      status s ppa = status s' ppa`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [add_kernel_mapping_h_def] THEN
   STRIP_TAC THEN
   POP_ASSUM MP_TAC THEN
   POP_ASSUM (MP_TAC o SPEC `ppa : physical_page_address`) THEN
   POP_ASSUM_LIST (K ALL_TAC) THEN
   COND_CASES_TAC THEN
   REWRITE_TAC []);;

export_thm add_kernel_mapping_h_status;;

let add_kernel_mapping_h_is_page_table = prove
  (`!s s' pr vr ppa.
      wellformed s /\
      add_kernel_mapping_h pr vr s s' ==>
      is_page_table (status s ppa) =
      is_page_table (status s' ppa)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [add_kernel_mapping_h_def] THEN
   STRIP_TAC THEN
   POP_ASSUM (MP_TAC o SPEC `ppa : physical_page_address`) THEN
   (COND_CASES_TAC THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th])) THEN
   MATCH_MP_TAC table_mapped_in_directory_is_page_table THEN
   EXISTS_TAC `reference s` THEN
   CONJ_TAC THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm add_kernel_mapping_h_is_page_table;;

let add_kernel_mapping_h_status_not_table = prove
  (`!s s' pr vr ppa.
      wellformed s /\
      add_kernel_mapping_h pr vr s s' /\
      ~is_page_table (status s ppa) ==>
      status s ppa = status s' ppa`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC add_kernel_mapping_h_status THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC [CONTRAPOS_THM] THEN
   STRIP_TAC THEN
   MATCH_MP_TAC table_mapped_in_directory_is_page_table THEN
   EXISTS_TAC `reference s` THEN
   ASM_REWRITE_TAC []);;

export_thm add_kernel_mapping_h_status_not_table;;

let add_kernel_mapping_h_dest_page_directory = prove
  (`!s s' pr vr ppa.
      wellformed s /\
      add_kernel_mapping_h pr vr s s' ==>
      dest_page_directory (status s ppa) =
      dest_page_directory (status s' ppa)`,
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `is_page_table (status s ppa)` THENL
   [MP_TAC (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
                   `vr : virtual_region`; `ppa : physical_page_address`]
              add_kernel_mapping_h_is_page_table) THEN
    ASM_REWRITE_TAC [] THEN
    POP_ASSUM MP_TAC THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN
    REWRITE_TAC [is_page_table_def] THEN
    (page_cases_tac `status s ppa` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [dest_page_table_def; is_some_def; dest_page_directory_def]) THEN
    (page_cases_tac `status s' ppa` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [dest_page_table_def; is_some_def; dest_page_directory_def]);
    AP_TERM_TAC THEN
    MATCH_MP_TAC add_kernel_mapping_h_status_not_table THEN
    EXISTS_TAC `pr : physical_region` THEN
    EXISTS_TAC `vr : virtual_region` THEN
    ASM_REWRITE_TAC []]);;

export_thm add_kernel_mapping_h_dest_page_directory;;

let add_kernel_mapping_h_is_page_directory = prove
  (`!s s' pr vr ppa.
      wellformed s /\
      add_kernel_mapping_h pr vr s s' ==>
      is_page_directory (status s ppa) =
      is_page_directory (status s' ppa)`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [is_page_directory_def] THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC add_kernel_mapping_h_dest_page_directory THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC []);;

export_thm add_kernel_mapping_h_is_page_directory;;

let add_kernel_mapping_h_dest_environment = prove
  (`!s s' pr vr ppa.
      wellformed s /\
      add_kernel_mapping_h pr vr s s' ==>
      dest_environment (status s ppa) =
      dest_environment (status s' ppa)`,
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `is_page_table (status s ppa)` THENL
   [MP_TAC (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
                   `vr : virtual_region`; `ppa : physical_page_address`]
              add_kernel_mapping_h_is_page_table) THEN
    ASM_REWRITE_TAC [] THEN
    POP_ASSUM MP_TAC THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN
    REWRITE_TAC [is_page_table_def] THEN
    (page_cases_tac `status s ppa` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [dest_page_table_def; is_some_def; dest_environment_def]) THEN
    (page_cases_tac `status s' ppa` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [dest_page_table_def; is_some_def; dest_environment_def]);
    AP_TERM_TAC THEN
    MATCH_MP_TAC add_kernel_mapping_h_status_not_table THEN
    EXISTS_TAC `pr : physical_region` THEN
    EXISTS_TAC `vr : virtual_region` THEN
    ASM_REWRITE_TAC []]);;

export_thm add_kernel_mapping_h_dest_environment;;

let add_kernel_mapping_h_is_environment = prove
  (`!s s' pr vr ppa.
      wellformed s /\
      add_kernel_mapping_h pr vr s s' ==>
      is_environment (status s ppa) =
      is_environment (status s' ppa)`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [is_environment_def] THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC add_kernel_mapping_h_dest_environment THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC []);;

export_thm add_kernel_mapping_h_is_environment;;

let add_kernel_mapping_h_dest_normal = prove
  (`!s s' pr vr ppa.
      wellformed s /\
      add_kernel_mapping_h pr vr s s' ==>
      dest_normal (status s ppa) =
      dest_normal (status s' ppa)`,
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `is_page_table (status s ppa)` THENL
   [MP_TAC (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
                   `vr : virtual_region`; `ppa : physical_page_address`]
              add_kernel_mapping_h_is_page_table) THEN
    ASM_REWRITE_TAC [] THEN
    POP_ASSUM MP_TAC THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN
    REWRITE_TAC [is_page_table_def] THEN
    (page_cases_tac `status s ppa` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [dest_page_table_def; is_some_def; dest_normal_def]) THEN
    (page_cases_tac `status s' ppa` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [dest_page_table_def; is_some_def; dest_normal_def]);
    AP_TERM_TAC THEN
    MATCH_MP_TAC add_kernel_mapping_h_status_not_table THEN
    EXISTS_TAC `pr : physical_region` THEN
    EXISTS_TAC `vr : virtual_region` THEN
    ASM_REWRITE_TAC []]);;

export_thm add_kernel_mapping_h_dest_normal;;

let add_kernel_mapping_h_is_normal = prove
  (`!s s' pr vr ppa.
      wellformed s /\
      add_kernel_mapping_h pr vr s s' ==>
      is_normal (status s ppa) =
      is_normal (status s' ppa)`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [is_normal_def] THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC add_kernel_mapping_h_dest_normal THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC []);;

export_thm add_kernel_mapping_h_is_normal;;

let add_kernel_mapping_h_dest_environment_or_normal = prove
  (`!s s' pr vr ppa.
      wellformed s /\
      add_kernel_mapping_h pr vr s s' ==>
      dest_environment_or_normal (status s ppa) =
      dest_environment_or_normal (status s' ppa)`,
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `is_page_table (status s ppa)` THENL
   [MP_TAC (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
                   `vr : virtual_region`; `ppa : physical_page_address`]
              add_kernel_mapping_h_is_page_table) THEN
    ASM_REWRITE_TAC [] THEN
    POP_ASSUM MP_TAC THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN
    REWRITE_TAC [is_page_table_def] THEN
    (page_cases_tac `status s ppa` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [dest_page_table_def; is_some_def; dest_environment_or_normal_def]) THEN
    (page_cases_tac `status s' ppa` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC
       [dest_page_table_def; is_some_def; dest_environment_or_normal_def]);
    AP_TERM_TAC THEN
    MATCH_MP_TAC add_kernel_mapping_h_status_not_table THEN
    EXISTS_TAC `pr : physical_region` THEN
    EXISTS_TAC `vr : virtual_region` THEN
    ASM_REWRITE_TAC []]);;

export_thm add_kernel_mapping_h_dest_environment_or_normal;;

let add_kernel_mapping_h_table_mapped_in_directory = prove
  (`!s s' pr vr pd pt.
      wellformed s /\
      add_kernel_mapping_h pr vr s s' ==>
      table_mapped_in_directory s pd pt =
      table_mapped_in_directory s' pd pt`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [table_mapped_in_directory_def] THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC add_kernel_mapping_h_dest_page_directory THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC []);;

export_thm add_kernel_mapping_h_table_mapped_in_directory;;

let add_kernel_mapping_h_table_mapped_in_reference = prove
  (`!s s' pr vr pt.
      wellformed s /\
      add_kernel_mapping_h pr vr s s' ==>
      table_mapped_in_directory s (reference s) pt =
      table_mapped_in_directory s' (reference s') pt`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `reference s = reference s'` SUBST1_TAC THENL
   [MATCH_MP_TAC add_kernel_mapping_h_reference THEN
    EXISTS_TAC `pr : physical_region` THEN
    EXISTS_TAC `vr : virtual_region` THEN
    ASM_REWRITE_TAC [];
    MATCH_MP_TAC add_kernel_mapping_h_table_mapped_in_directory THEN
    EXISTS_TAC `pr : physical_region` THEN
    EXISTS_TAC `vr : virtual_region` THEN
    ASM_REWRITE_TAC []]);;

export_thm add_kernel_mapping_h_table_mapped_in_reference;;

let add_kernel_mapping_h_translate_user_page = prove
  (`!s s' pr vr pd vpa.
      wellformed s /\
      wellformed s' /\
      add_kernel_mapping_h pr vr s s' /\
      is_user_page_address vpa ==>
      translate_page s pd vpa = translate_page s' pd vpa`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [translate_page_def] THEN
   virtual_page_address_cases_tac `vpa : virtual_page_address` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [LET_DEF; LET_END_DEF; virtual_page_address_tybij] THEN
   MP_TAC (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
                  `vr : virtual_region`; `pd : page_directory`]
             add_kernel_mapping_h_dest_page_directory) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   (page_cases_tac `status s pd` THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [case_option_def; dest_page_directory_def]) THEN
   page_directory_data_cases_tac `pdd : page_directory_data` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [page_directory_data_tybij] THEN
   option_cases_tac
     `(f : page_directory_index -> page_directory_entry option) vsa` THENL
   [STRIP_TAC THEN
    ASM_REWRITE_TAC [case_option_def];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `pde : page_directory_entry` ASSUME_TAC) THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   (page_directory_entry_cases_tac `pde : page_directory_entry` THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [case_page_directory_entry_def]) THEN
   ASM_CASES_TAC `table_mapped_in_directory s (reference s) pt` THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `NONE : physical_page_address option` THEN
    CONJ_TAC THENL
    [POP_ASSUM (MP_TAC o REWRITE_RULE [table_mapped_in_directory_def]) THEN
     (page_cases_tac `status s (reference s)` THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC [case_option_def; dest_page_directory_def]) THEN
     STRIP_TAC THEN
     (page_cases_tac `status s pt` THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC [case_option_def; dest_page_table_def]) THEN
     option_cases_tac `dest_page_table_data ptd si` THENL
     [DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [case_option_def];
      ALL_TAC] THEN
     DISCH_THEN (X_CHOOSE_THEN `ppa : physical_page_address` ASSUME_TAC) THEN
     SUBGOAL_THEN `F` CONTR_TAC THEN
     UNDISCH_TAC `is_user_page_address vpa` THEN
     REWRITE_TAC [is_user_page_address_def] THEN
     ASM_CASES_TAC `is_kernel_superpage_address vsa` THENL
     [ASM_REWRITE_TAC
        [is_kernel_page_address_def; virtual_page_address_tybij] THEN
      ASM_REWRITE_TAC [LET_DEF; LET_END_DEF];
      ALL_TAC] THEN
     MATCH_MP_TAC reference_maps_kernel_addresses THEN
     EXISTS_TAC `s : state` THEN
     ASM_REWRITE_TAC
       [mapped_page_def; translate_page_def; virtual_page_address_tybij] THEN
     REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
     ASM_REWRITE_TAC [dest_page_directory_def; case_option_def] THEN
     MP_TAC (SPECL
               [`s : state`;
                `pt : page_table`;
                `pd : page_directory`;
                `reference s`;
                `pdd : page_directory_data`;
                `pdd' : page_directory_data`;
                `vsa : virtual_superpage_address`;
                `pdi : virtual_superpage_address`]
               no_shared_page_tables) THEN
     ASM_REWRITE_TAC [dest_page_directory_def; page_directory_data_tybij] THEN
     DISCH_THEN (CONJUNCTS_THEN2 SUBST_VAR_TAC SUBST_VAR_TAC) THEN
     ASM_REWRITE_TAC
       [case_option_def; case_page_directory_entry_def; dest_page_table_def;
        is_some_def];
     MATCH_MP_TAC EQ_SYM THEN
     MP_TAC (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
                    `vr : virtual_region`; `pt : page_table`]
               add_kernel_mapping_h_table_mapped_in_reference) THEN
     ASM_REWRITE_TAC [] THEN
     POP_ASSUM (K ALL_TAC) THEN
     REWRITE_TAC [table_mapped_in_directory_def] THEN
     (page_cases_tac `status s' (reference s')` THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC [case_option_def; dest_page_directory_def]) THEN
     STRIP_TAC THEN
     (page_cases_tac `status s' pt` THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC [case_option_def; dest_page_table_def]) THEN
     option_cases_tac `dest_page_table_data ptd si` THENL
     [DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [case_option_def];
      ALL_TAC] THEN
     DISCH_THEN (X_CHOOSE_THEN `ppa : physical_page_address` ASSUME_TAC) THEN
     SUBGOAL_THEN `F` CONTR_TAC THEN
     UNDISCH_TAC `is_user_page_address vpa` THEN
     REWRITE_TAC [is_user_page_address_def] THEN
     ASM_CASES_TAC `is_kernel_superpage_address vsa` THENL
     [ASM_REWRITE_TAC
        [is_kernel_page_address_def; virtual_page_address_tybij] THEN
      ASM_REWRITE_TAC [LET_DEF; LET_END_DEF];
      ALL_TAC] THEN
     MATCH_MP_TAC reference_maps_kernel_addresses THEN
     EXISTS_TAC `s' : state` THEN
     ASM_REWRITE_TAC
       [mapped_page_def; translate_page_def; virtual_page_address_tybij] THEN
     REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
     ASM_REWRITE_TAC [dest_page_directory_def; case_option_def] THEN
     MP_TAC (SPECL
               [`s' : state`;
                `pt : page_table`;
                `pd : page_directory`;
                `reference s'`;
                `pdd : page_directory_data`;
                `pdd' : page_directory_data`;
                `vsa : virtual_superpage_address`;
                `pdi : virtual_superpage_address`]
               no_shared_page_tables) THEN
     ASM_REWRITE_TAC [dest_page_directory_def; page_directory_data_tybij] THEN
     ANTS_TAC THENL
     [SUBGOAL_THEN
        `dest_page_directory (status s pd) =
         dest_page_directory (status s' pd)` (SUBST1_TAC o SYM) THENL
      [MATCH_MP_TAC add_kernel_mapping_h_dest_page_directory THEN
       EXISTS_TAC `pr : physical_region` THEN
       EXISTS_TAC `vr : virtual_region` THEN
       ASM_REWRITE_TAC [];
       ASM_REWRITE_TAC [dest_page_directory_def; page_directory_data_tybij]];
      ALL_TAC] THEN
     DISCH_THEN (CONJUNCTS_THEN2 SUBST_VAR_TAC SUBST_VAR_TAC) THEN
     ASM_REWRITE_TAC
       [case_option_def; case_page_directory_entry_def; dest_page_table_def;
        is_some_def]];
    SUBGOAL_THEN `status s pt = status s' pt` (fun th -> REWRITE_TAC [th]) THEN
    MATCH_MP_TAC add_kernel_mapping_h_status THEN
    EXISTS_TAC `pr : physical_region` THEN
    EXISTS_TAC `vr : virtual_region` THEN
    ASM_REWRITE_TAC []]);;

export_thm add_kernel_mapping_h_translate_user_page;;

let add_kernel_mapping_h_translate_page = prove
  (`!s s' pr vr pd vpa.
      wellformed s /\
      wellformed s' /\
      add_kernel_mapping_h pr vr s s' /\
      ~member_virtual_region vpa vr ==>
      translate_page s pd vpa = translate_page s' pd vpa`,
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `is_page_directory (status s pd)` THENL
   [ASM_CASES_TAC `is_kernel_page_address vpa` THENL
    [MP_TAC (SPECL [`s : state`; `pd : page_directory`;
                    `vpa : virtual_page_address`]
               page_directories_contain_reference) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC [];
      ALL_TAC] THEN
     DISCH_THEN SUBST1_TAC THEN
     MP_TAC (SPECL [`s' : state`; `pd : page_directory`;
                    `vpa : virtual_page_address`]
               page_directories_contain_reference) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN
      MP_TAC (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
                     `vr : virtual_region`; `pd : page_directory`]
                add_kernel_mapping_h_is_page_directory) THEN
      ASM_REWRITE_TAC [];
      ALL_TAC] THEN
     DISCH_THEN SUBST1_TAC THEN
     FIRST_X_ASSUM
       (STRIP_ASSUME_TAC o CONV_RULE (REWR_CONV add_kernel_mapping_h_def)) THEN
     MATCH_MP_TAC EQ_SYM THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     FIRST_ASSUM ACCEPT_TAC;
     MATCH_MP_TAC add_kernel_mapping_h_translate_user_page THEN
     EXISTS_TAC `pr : physical_region` THEN
     EXISTS_TAC `vr : virtual_region` THEN
     ASM_REWRITE_TAC [is_user_page_address_def]];
    MP_TAC (SPECL
              [`s : state`; `pd : page_directory`; `vpa : virtual_page_address`]
              translate_page_is_not_page_directory) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC translate_page_is_not_page_directory THEN
    MP_TAC (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
                   `vr : virtual_region`; `pd : page_directory`]
              add_kernel_mapping_h_is_page_directory) THEN
    ASM_REWRITE_TAC []]);;

export_thm add_kernel_mapping_h_translate_page;;

let add_kernel_mapping_h_translate_page_cr3 = prove
  (`!s s' pr vr vpa.
      wellformed s /\
      wellformed s' /\
      add_kernel_mapping_h pr vr s s' /\
      ~member_virtual_region vpa vr ==>
      translate_page s (cr3 s) vpa = translate_page s' (cr3 s') vpa`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL
             [`s : state`;
              `s' : state`;
              `pr : physical_region`;
              `vr : virtual_region`]
             add_kernel_mapping_h_cr3) THEN
   ANTS_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC add_kernel_mapping_h_translate_page THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC []);;

export_thm add_kernel_mapping_h_translate_page_cr3;;

let add_kernel_mapping_h_translate_mapped_page = prove
  (`!s s' pr vr vpa.
      add_kernel_mapping_h pr vr s s' /\
      member_virtual_region vpa vr ==>
      ?ppa.
         member_physical_region ppa pr /\
         translate_page s' (reference s') vpa = SOME ppa`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC
     [add_kernel_mapping_h_def; member_virtual_region_def;
      member_physical_region_def] THEN
   STRIP_TAC THEN
   POP_ASSUM MP_TAC THEN
   POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM MP_TAC THEN
   POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM MP_TAC THEN
   POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [GSYM ALL_MEM; mem_nth; I_THM] THEN
   REPEAT STRIP_TAC THEN
   EXISTS_TAC `nth (physical_region_to_list pr) i` THEN
   SUBGOAL_THEN
     `LENGTH (physical_region_to_list pr) =
      LENGTH (virtual_region_to_list vr)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC
      [length_physical_region_to_list; length_virtual_region_to_list];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [EXISTS_TAC `i : num` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `i : num` THEN
   CONJ_TAC THENL
   [MP_TAC (ISPECL
              [`\vpa ppa. translate_page s' (reference s') vpa = SOME ppa`;
               `virtual_region_to_list vr`;
               `physical_region_to_list pr`;
               `LENGTH (virtual_region_to_list vr)`]
              length_zipwith) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    MP_TAC (ISPECL
              [`\vpa ppa. translate_page s' (reference s') vpa = SOME ppa`;
               `virtual_region_to_list vr`;
               `physical_region_to_list pr`;
               `LENGTH (virtual_region_to_list vr)`;
               `i : num`]
              nth_zipwith) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    REFL_TAC]);;

export_thm add_kernel_mapping_h_translate_mapped_page;;

let add_kernel_mapping_h_translate_mapped_page_cr3 = prove
  (`!s s' pr vr vpa.
      wellformed s' /\
      add_kernel_mapping_h pr vr s s' /\
      member_virtual_region vpa vr ==>
      ?ppa.
         member_physical_region ppa pr /\
         translate_page s' (cr3 s') vpa = SOME ppa`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL
             [`s' : state`;
              `cr3 s'`;
              `vpa : virtual_page_address`]
             page_directories_contain_reference) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC cr3_is_page_directory THEN
     FIRST_ASSUM ACCEPT_TAC;
     MATCH_MP_TAC is_kernel_region THEN
     EXISTS_TAC `vr : virtual_region` THEN
     POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
     POP_ASSUM MP_TAC THEN
     REWRITE_TAC [add_kernel_mapping_h_def] THEN
     STRIP_TAC];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC add_kernel_mapping_h_translate_mapped_page THEN
   EXISTS_TAC `s : state` THEN
   EXISTS_TAC `vr : virtual_region` THEN
   ASM_REWRITE_TAC []);;

export_thm add_kernel_mapping_h_translate_mapped_page_cr3;;

(* execute_h *)

let execute_h_status = prove
  (`!s s' pd. execute_h pd s s' ==> status s = status s'`,
   REWRITE_TAC [execute_h_def] THEN
   REPEAT STRIP_TAC);;

export_thm execute_h_status;;

let execute_h_reference = prove
  (`!s s' pd.
      execute_h pd s s' ==> reference s = reference s'`,
   REWRITE_TAC [execute_h_def] THEN
   REPEAT STRIP_TAC);;

export_thm execute_h_reference;;

let execute_h_regions = prove
  (`!s s' pd. execute_h pd s s' ==> regions s = regions s'`,
   REWRITE_TAC [execute_h_def] THEN
   REPEAT STRIP_TAC);;

export_thm execute_h_regions;;

let execute_h_translate_page = prove
  (`!s s' pd.
      execute_h pd s s' ==>
      translate_page s = translate_page s'`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC status_translate_page THEN
   MATCH_MP_TAC execute_h_status THEN
   EXISTS_TAC `pd : page_directory` THEN
   ASM_REWRITE_TAC []);;

export_thm execute_h_translate_page;;

(* write_k *)

let write_k_status = prove
  (`!s s' va b ppa.
      write_k va b s s' /\
      (~is_normal (status s ppa) \/
       ~is_normal (status s' ppa)) ==>
      status s ppa = status s' ppa`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [write_k_def] THEN
   DISCH_THEN
     (fun th ->
        STRIP_ASSUME_TAC (CONJUNCT1 th) THEN
        MP_TAC (CONJUNCT2 th)) THEN
   POP_ASSUM MP_TAC THEN
   option_cases_tac `translation s va` THENL
   [STRIP_TAC THEN
    ASM_REWRITE_TAC [case_option_def];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `pa : physical_address` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   PAIR_CASES_TAC `dest_physical_address pa` THEN
   DISCH_THEN
    (X_CHOOSE_THEN `ppa' : physical_page_address`
      (X_CHOOSE_THEN `i : page_offset` STRIP_ASSUME_TAC)) THEN
   ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
   DISCH_THEN (MP_TAC o SPEC `ppa : physical_page_address`) THEN
   COND_CASES_TAC THENL
   [POP_ASSUM (SUBST_VAR_TAC o SYM) THEN
    page_cases_tac `status s ppa` THEN
    STRIP_TAC THEN
    page_cases_tac `status s' ppa` THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC
      [is_normal_def; dest_normal_def; case_option_def; page_distinct;
       page_inj; option_distinct; is_some_def];
    DISCH_THEN (fun th -> REWRITE_TAC [th])]);;

export_thm write_k_status;;

let write_k_translate_page = prove
  (`!s s' va b.
      write_k va b s s' ==>
      translate_page s = translate_page s'`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC translate_page_inj THEN
   GEN_TAC THEN
   DISCH_THEN ASSUME_TAC THEN
   MATCH_MP_TAC write_k_status THEN
   EXISTS_TAC `va : virtual_address` THEN
   EXISTS_TAC `b : byte` THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM MP_TAC THEN
   MP_TAC (SPEC `status s ppa` page_cases) THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `status s' ppa` page_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_page_directory_or_table_def; is_page_directory_def;
      is_page_table_def; dest_page_directory_def; is_some_def;
      dest_page_table_def; dest_normal_def; case_option_def; page_distinct;
      page_inj; option_distinct; is_normal_def]);;

export_thm write_k_translate_page;;

let write_k_cr3 = prove
  (`!s s' va b. write_k va b s s' ==> cr3 s = cr3 s'`,
   REWRITE_TAC [write_k_def] THEN
   REPEAT STRIP_TAC);;

export_thm write_k_cr3;;

let write_k_regions = prove
  (`!s s' va b. write_k va b s s' ==> regions s = regions s'`,
   REWRITE_TAC [write_k_def] THEN
   REPEAT STRIP_TAC);;

export_thm write_k_regions;;

let write_k_reference = prove
  (`!s s' va b. write_k va b s s' ==> reference s = reference s'`,
   REWRITE_TAC [write_k_def] THEN
   REPEAT STRIP_TAC);;

export_thm write_k_reference;;

let write_k_translate_page_cr3 = prove
  (`!s s' va b.
      write_k va b s s' ==>
      translate_page s (cr3 s) = translate_page s' (cr3 s')`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_k_translate_page) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_k_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

export_thm write_k_translate_page_cr3;;

let write_k_dest_environment = prove
  (`!s s' va b ppa.
      write_k va b s s' ==>
      dest_environment (status s ppa) = dest_environment (status s' ppa)`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`;
             `ppa : physical_page_address`]
      write_k_status) THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC (SPEC `status s ppa` page_cases) THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `status s' ppa` page_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [dest_normal_def; dest_environment_def; case_option_def; page_distinct;
      is_some_def; page_inj; option_distinct; is_normal_def] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

export_thm write_k_dest_environment;;

let write_k_is_environment = prove
  (`!s s' va b ppa.
      write_k va b s s' ==>
      is_environment (status s ppa) = is_environment (status s' ppa)`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [is_environment_def] THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC write_k_dest_environment THEN
   EXISTS_TAC `va : virtual_address` THEN
   EXISTS_TAC `b : byte` THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm write_k_is_environment;;

let write_k_status_update = prove
  (`!s s' va b.
      write_k va b s s' ==>
      ?vpa i ppa d.
        va = mk_virtual_address (vpa,i) /\
        translate_page s (cr3 s) vpa = SOME ppa /\
        status s ppa = Normal d /\
        !ppa'.
           status s' ppa' =
             if ppa' = ppa then Normal (update_page_data i b d)
             else status s ppa'`,
   REPEAT GEN_TAC THEN
   virtual_address_cases_tac `va : virtual_address` THEN
   REPEAT STRIP_TAC THEN
   EXISTS_TAC `vpa : virtual_page_address` THEN
   EXISTS_TAC `i : page_offset` THEN
   FIRST_ASSUM (MP_TAC o CONV_RULE (REWR_CONV write_k_def)) THEN
   DISCH_THEN (MP_TAC o CONJUNCT2 o REWRITE_RULE [CONJ_ASSOC]) THEN
   ASM_REWRITE_TAC [translation_def; virtual_address_tybij] THEN
   REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
   option_cases_tac `translate_page s (cr3 s) vpa` THENL
   [STRIP_TAC THEN
    ASM_REWRITE_TAC [case_option_def];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `ppa : physical_page_address` ASSUME_TAC) THEN
   ASM_REWRITE_TAC [case_option_def; physical_address_tybij] THEN
   STRIP_TAC THEN
   EXISTS_TAC `ppa : physical_page_address` THEN
   FIRST_ASSUM (MP_TAC o SPEC `ppa : physical_page_address`) THEN
   REWRITE_TAC [] THEN
   page_cases_tac `status s ppa` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_environment_def; dest_environment_def;
      is_normal_def; dest_normal_def;
      is_page_table_def; dest_page_table_def;
      is_page_directory_def; dest_page_directory_def;
      is_some_def; option_distinct; option_inj; case_option_def] THEN
   page_cases_tac `status s' ppa` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_environment_def; dest_environment_def;
      is_normal_def; dest_normal_def;
      is_page_table_def; dest_page_table_def;
      is_page_directory_def; dest_page_directory_def;
      is_some_def; option_distinct; option_inj; case_option_def] THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   EXISTS_TAC `d : page_data` THEN
   REWRITE_TAC [] THEN
   X_GEN_TAC `ppa' : physical_page_address` THEN
   COND_CASES_TAC THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `ppa' : physical_page_address`) THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_ACCEPT_TAC EQ_SYM);;

export_thm write_k_status_update;;

let write_k_view_k = prove
  (`!va b. ?f. !s s'.
      wellformed s /\
      wellformed s' /\
      write_k va b s s' ==>
      view KDomain s' = f (view KDomain s)`,
   REPEAT STRIP_TAC THEN
   REPEAT GEN_TAC THEN
   virtual_address_cases_tac `va : virtual_address` THEN
   STRIP_TAC THEN
   REWRITE_TAC [view_def] THEN
   MP_TAC
     (ISPEC
        `\f g.
           KView
             (mk_observable_pages
                (\vpa'.
                   case_option
                     NONE
                     (\ (d,vpas).
                        SOME
                          ((if vpa IN vpas then update_page_data i b d else d),
                           vpas))
                     (dest_observable_pages f vpa'))) g`
        view_k_recursion) THEN
   STRIP_TAC THEN
   EXISTS_TAC `fn : view -> view` THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (CONV_TAC o RAND_CONV o REWR_CONV) THEN
   REWRITE_TAC
     [view_inj; mk_observable_pages_k_def; mk_region_handles_k_def;
      translate_to_observable_pages_def;
      mk_observable_pages_inj; observable_pages_tybij] THEN
   CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC write_k_regions THEN
    EXISTS_TAC `va : virtual_address` THEN
    EXISTS_TAC `b : byte` THEN
    FIRST_ASSUM ACCEPT_TAC] THEN
   X_GEN_TAC `vpa' : virtual_page_address` THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_k_translate_page_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MP_TAC
     (SPECL
        [`s : state`;
         `s' : state`;
         `va : virtual_address`;
         `b : byte`]
      write_k_status_update) THEN
   ASM_REWRITE_TAC [mk_virtual_address_inj; PAIR_EQ] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM (SUBST_VAR_TAC o SYM) THEN
   FIRST_X_ASSUM (SUBST_VAR_TAC o SYM) THEN
   ASM_REWRITE_TAC [] THEN
   option_cases_tac `translate_page s (cr3 s) vpa'` THENL
   [DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [case_option_def];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `ppa' : physical_page_address` ASSUME_TAC) THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   ASM_CASES_TAC `ppa' = (ppa : physical_page_address)` THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    ASM_REWRITE_TAC
      [is_normal_def; dest_normal_def; is_some_def;
       case_option_def; dest_environment_or_normal_def; IN_ELIM;
       option_inj; PAIR_EQ; EXTENSION];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   page_cases_tac `status s ppa'` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_environment_def; dest_environment_def;
      is_normal_def; dest_normal_def; dest_environment_or_normal_def;
      is_page_table_def; dest_page_table_def; IN_ELIM;
      is_page_directory_def; dest_page_directory_def;
      is_some_def; option_distinct; option_inj; case_option_def]);;

export_thm write_k_view_k;;

(* write_u *)

let write_u_status = prove
  (`!s s' va b ppa.
      write_u va b s s' /\
      (~is_normal (status s ppa) \/
       ~is_normal (status s' ppa)) ==>
      status s ppa = status s' ppa`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [write_u_def] THEN
   DISCH_THEN
     (fun th ->
        STRIP_ASSUME_TAC (CONJUNCT1 th) THEN
        MP_TAC (CONJUNCT2 th)) THEN
   POP_ASSUM MP_TAC THEN
   option_cases_tac `translation s va` THENL
   [STRIP_TAC THEN
    ASM_REWRITE_TAC [case_option_def];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `pa : physical_address` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   PAIR_CASES_TAC `dest_physical_address pa` THEN
   DISCH_THEN
    (X_CHOOSE_THEN `ppa' : physical_page_address`
      (X_CHOOSE_THEN `i : page_offset` STRIP_ASSUME_TAC)) THEN
   ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
   DISCH_THEN (MP_TAC o SPEC `ppa : physical_page_address`) THEN
   COND_CASES_TAC THENL
   [POP_ASSUM (SUBST_VAR_TAC o SYM) THEN
    page_cases_tac `status s ppa` THEN
    STRIP_TAC THEN
    page_cases_tac `status s' ppa` THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC
      [is_normal_def; dest_normal_def; case_option_def; page_distinct;
       page_inj; option_distinct; is_some_def];
    DISCH_THEN (fun th -> REWRITE_TAC [th])]);;

export_thm write_u_status;;

let write_u_translate_page = prove
  (`!s s' va b.
      write_u va b s s' ==>
      translate_page s = translate_page s'`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC translate_page_inj THEN
   GEN_TAC THEN
   DISCH_THEN ASSUME_TAC THEN
   MATCH_MP_TAC write_u_status THEN
   EXISTS_TAC `va : virtual_address` THEN
   EXISTS_TAC `b : byte` THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM MP_TAC THEN
   MP_TAC (SPEC `status s ppa` page_cases) THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `status s' ppa` page_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_page_directory_or_table_def; is_page_directory_def;
      is_page_table_def; dest_page_directory_def; is_some_def;
      dest_page_table_def; dest_normal_def; case_option_def; page_distinct;
      page_inj; option_distinct; is_normal_def]);;

export_thm write_u_translate_page;;

let write_u_cr3 = prove
  (`!s s' va b. write_u va b s s' ==> cr3 s = cr3 s'`,
   REWRITE_TAC [write_u_def] THEN
   REPEAT STRIP_TAC);;

export_thm write_u_cr3;;

let write_u_regions = prove
  (`!s s' va b. write_u va b s s' ==> regions s = regions s'`,
   REWRITE_TAC [write_u_def] THEN
   REPEAT STRIP_TAC);;

export_thm write_u_regions;;

let write_u_reference = prove
  (`!s s' va b. write_u va b s s' ==> reference s = reference s'`,
   REWRITE_TAC [write_u_def] THEN
   REPEAT STRIP_TAC);;

export_thm write_u_reference;;

let write_u_translate_page_cr3 = prove
  (`!s s' va b.
      write_u va b s s' ==>
      translate_page s (cr3 s) = translate_page s' (cr3 s')`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_u_translate_page) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_u_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

export_thm write_u_translate_page_cr3;;

let write_u_dest_environment = prove
  (`!s s' va b ppa.
      write_u va b s s' ==>
      dest_environment (status s ppa) = dest_environment (status s' ppa)`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`;
             `ppa : physical_page_address`]
      write_u_status) THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC (SPEC `status s ppa` page_cases) THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `status s' ppa` page_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [dest_normal_def; dest_environment_def; case_option_def; page_distinct;
      is_some_def; page_inj; option_distinct; is_normal_def] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

export_thm write_u_dest_environment;;

let write_u_is_environment = prove
  (`!s s' va b ppa.
      write_u va b s s' ==>
      is_environment (status s ppa) = is_environment (status s' ppa)`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [is_environment_def] THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC write_u_dest_environment THEN
   EXISTS_TAC `va : virtual_address` THEN
   EXISTS_TAC `b : byte` THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm write_u_is_environment;;

(* ~~~~~~ *)
(* Output *)
(* ~~~~~~ *)

(* ~~~~~~~~~~~~~~~~~~~~~~ *)
(* System security policy *)
(* ~~~~~~~~~~~~~~~~~~~~~~ *)

(* Local respect *)

let local_respect_write_e_view_u = prove
  (`!s s' va b.
      wellformed s /\
      wellformed s' /\
      write_e va b s s' ==>
      view UDomain s = view UDomain s'`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC
     [view_def; view_inj; mk_observable_pages_u_def;
      translate_to_observable_pages_def] THEN
   AP_TERM_TAC THEN
   ABS_TAC THEN
   (COND_CASES_TAC THEN
    ASM_REWRITE_TAC [case_option_def]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_e_translate_page_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   option_cases_tac `translate_page s (cr3 s) vpa` THENL
   [DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [case_option_def];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `ppa : physical_page_address` ASSUME_TAC) THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC write_e_dest_environment_or_normal THEN
   EXISTS_TAC `va : virtual_address` THEN
   EXISTS_TAC `b : byte` THEN
   EXISTS_TAC `cr3 s` THEN
   EXISTS_TAC `vpa : virtual_page_address` THEN
   ASM_REWRITE_TAC []);;

let local_respect_derive_region_h_view_e = prove
  (`!s s' pr ppa l.
      derive_region_h pr ppa l s s' ==>
      view EDomain s = view EDomain s'`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC
     [view_def; view_inj; mk_observable_pages_e_def;
      translate_to_observable_pages_def] THEN
   AP_TERM_TAC THEN
   ABS_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
             `ppa : physical_page_address`; `l : region_length`]
      derive_region_h_translate_page_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
             `ppa : physical_page_address`; `l : region_length`]
      derive_region_h_status) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   REFL_TAC);;

let local_respect_allocate_page_directory_h_view_e = prove
  (`!s s' ppa.
      wellformed s /\ allocate_page_directory_h ppa s s' ==>
      view EDomain s = view EDomain s'`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC
     [view_def; view_inj; mk_observable_pages_e_def;
      translate_to_observable_pages_def] THEN
   AP_TERM_TAC THEN
   ABS_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `ppa : physical_page_address`]
      allocate_page_directory_h_translate_page_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `ppa : physical_page_address`]
      allocate_page_directory_h_is_environment) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   option_cases_tac `translate_page s' (cr3 s') vpa` THENL
   [DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [case_option_def];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `ppa' : physical_page_address` SUBST1_TAC) THEN
   REWRITE_TAC [case_option_def] THEN
   (ASM_CASES_TAC `is_environment (status s ppa')` THEN
    ASM_REWRITE_TAC [case_option_def]) THEN
   AP_TERM_TAC THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC allocate_page_directory_h_status THEN
   EXISTS_TAC `ppa : physical_page_address` THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   POP_ASSUM MP_TAC THEN
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC [allocate_page_directory_h_def; unmapped_normal_page_def] THEN
   STRIP_TAC THEN
   POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM MP_TAC THEN
   POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [is_normal_page_def] THEN
   page_cases_tac `status s ppa` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_environment_def; is_normal_def; dest_normal_def;
      dest_environment_def; is_some_def]);;

let local_respect_free_page_directory_h_view_e = prove
  (`!s s' pd.
      wellformed s' /\ free_page_directory_h pd s s' ==>
      view EDomain s = view EDomain s'`,
   REWRITE_TAC [free_page_directory_h_def] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC local_respect_allocate_page_directory_h_view_e THEN
   EXISTS_TAC `pd : page_directory` THEN
   ASM_REWRITE_TAC []);;

let local_respect_add_mapping_h_view_e = prove
  (`!s s' pd pts pr vr.
      wellformed s /\
      wellformed s' /\
      add_mapping_h pd pts pr vr s s' ==>
      view EDomain s = view EDomain s'`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC
     [view_def; view_inj; mk_observable_pages_e_def;
      translate_to_observable_pages_def] THEN
   AP_TERM_TAC THEN
   ABS_TAC THEN
   ASM_CASES_TAC `is_kernel_page_address vpa` THENL
   [MP_TAC
      (SPECL
         [`s : state`;
          `s' : state`;
          `pd : page_directory`;
          `pts : page_table list`;
          `pr : physical_region`;
          `vr : virtual_region`;
          `vpa : virtual_page_address`]
         add_mapping_h_translate_kernel_page_cr3) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    option_cases_tac `translate_page s (cr3 s) vpa` THENL
    [DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC [case_option_def];
     ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN `ppa : physical_page_address` ASSUME_TAC) THEN
    ASM_REWRITE_TAC [case_option_def] THEN
    MP_TAC
      (SPECL
         [`s : state`;
          `s' : state`;
          `pd : page_directory`;
          `pts : page_table list`;
          `pr : physical_region`;
          `vr : virtual_region`;
          `ppa : physical_page_address`]
         add_mapping_h_is_environment) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    ASM_CASES_TAC `is_environment (status s ppa)` THENL
    [ASM_REWRITE_TAC [case_option_def] THEN
     SUBGOAL_THEN
       `?d.
          status s ppa = Environment d /\
          status s' ppa = Environment d` STRIP_ASSUME_TAC THENL
     [POP_ASSUM MP_TAC THEN
      page_cases_tac `status s ppa` THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC
        [is_environment_def; dest_environment_def;
         is_normal_def; dest_normal_def;
         is_page_table_def; dest_page_table_def;
         is_page_directory_def; dest_page_directory_def;
         is_some_def; option_distinct; option_inj] THEN
      REWRITE_TAC [page_inj; UNWIND_THM1] THEN
      MP_TAC
        (SPECL
           [`s : state`;
            `s' : state`;
            `pd : page_directory`;
            `pts : page_table list`;
            `pr : physical_region`;
            `vr : virtual_region`;
            `ppa : physical_page_address`]
           add_mapping_h_dest_environment) THEN
      ASM_REWRITE_TAC [dest_environment_def] THEN
      page_cases_tac `status s' ppa` THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC
        [is_environment_def; dest_environment_def;
         is_normal_def; dest_normal_def;
         is_page_table_def; dest_page_table_def;
         is_page_directory_def; dest_page_directory_def;
         is_some_def; option_distinct; option_inj] THEN
      DISCH_THEN SUBST1_TAC THEN
      REFL_TAC;
      ALL_TAC] THEN
     ASM_REWRITE_TAC [dest_environment_or_normal_def; case_option_def] THEN
     AP_TERM_TAC THEN
     AP_TERM_TAC THEN
     MATCH_MP_TAC EXTENSION_IMP THEN
     X_GEN_TAC `vpa' : virtual_page_address` THEN
     ASM_REWRITE_TAC [IN_ELIM] THEN
     AP_THM_TAC THEN
     AP_TERM_TAC THEN
     ASM_CASES_TAC `is_kernel_page_address vpa'` THENL
     [MP_TAC
        (SPECL
           [`s : state`;
            `s' : state`;
            `pd : page_directory`;
            `pts : page_table list`;
            `pr : physical_region`;
            `vr : virtual_region`;
            `vpa' : virtual_page_address`]
           add_mapping_h_translate_kernel_page_cr3) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      option_cases_tac `translate_page s (cr3 s) vpa'` THENL
      [DISCH_THEN SUBST1_TAC THEN
       REWRITE_TAC [case_option_def];
       ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN `ppa' : physical_page_address` ASSUME_TAC) THEN
      ASM_REWRITE_TAC [case_option_def] THEN
      MP_TAC
        (SPECL
           [`s : state`;
            `s' : state`;
            `pd : page_directory`;
            `pts : page_table list`;
            `pr : physical_region`;
            `vr : virtual_region`;
            `ppa' : physical_page_address`]
           add_mapping_h_is_environment) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      REFL_TAC;
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `NONE : physical_page_address option` THEN
      CONJ_TAC THENL
      [option_cases_tac `translate_page s (cr3 s) vpa'` THENL
       [DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC [case_option_def];
        ALL_TAC] THEN
       DISCH_THEN (X_CHOOSE_THEN `ppa' : physical_page_address` ASSUME_TAC) THEN
       ASM_REWRITE_TAC [case_option_def] THEN
       MP_TAC
         (SPECL
            [`s : state`;
             `cr3 s`;
             `vpa' : virtual_page_address`;
             `ppa' : physical_page_address`]
            environment_only_kernel_addresses) THEN
       ASM_REWRITE_TAC [] THEN
       DISCH_THEN (SUBST1_TAC o EQF_INTRO) THEN
       REWRITE_TAC [];
       option_cases_tac `translate_page s' (cr3 s') vpa'` THENL
       [DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC [case_option_def];
        ALL_TAC] THEN
       DISCH_THEN (X_CHOOSE_THEN `ppa' : physical_page_address` ASSUME_TAC) THEN
       ASM_REWRITE_TAC [case_option_def] THEN
       MP_TAC
         (SPECL
            [`s' : state`;
             `cr3 s'`;
             `vpa' : virtual_page_address`;
             `ppa' : physical_page_address`]
            environment_only_kernel_addresses) THEN
       ASM_REWRITE_TAC [] THEN
       DISCH_THEN (SUBST1_TAC o EQF_INTRO) THEN
      REWRITE_TAC []]];
     ASM_REWRITE_TAC [case_option_def]];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `NONE : (page_data # virtual_page_address set) option` THEN
    CONJ_TAC THENL
     [option_cases_tac `translate_page s (cr3 s) vpa` THENL
      [DISCH_THEN SUBST1_TAC THEN
       REWRITE_TAC [case_option_def];
       ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN `ppa : physical_page_address` ASSUME_TAC) THEN
      ASM_REWRITE_TAC [case_option_def] THEN
      MP_TAC
        (SPECL
           [`s : state`;
            `cr3 s`;
            `vpa : virtual_page_address`;
            `ppa : physical_page_address`]
           environment_only_kernel_addresses) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (SUBST1_TAC o EQF_INTRO) THEN
      REWRITE_TAC [case_option_def];
      option_cases_tac `translate_page s' (cr3 s') vpa` THENL
      [DISCH_THEN SUBST1_TAC THEN
       REWRITE_TAC [case_option_def];
       ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN `ppa : physical_page_address` ASSUME_TAC) THEN
      ASM_REWRITE_TAC [case_option_def] THEN
      MP_TAC
        (SPECL
           [`s' : state`;
            `cr3 s'`;
            `vpa : virtual_page_address`;
            `ppa : physical_page_address`]
           environment_only_kernel_addresses) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (SUBST1_TAC o EQF_INTRO) THEN
      REWRITE_TAC [case_option_def]]]);;

let local_respect_remove_mapping_h_view_e = prove
  (`!s s' pd vr.
      wellformed s /\
      wellformed s' /\
      remove_mapping_h pd vr s s' ==>
      view EDomain s = view EDomain s'`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC
     [view_def; view_inj; mk_observable_pages_e_def;
      translate_to_observable_pages_def] THEN
   AP_TERM_TAC THEN
   ABS_TAC THEN
   ASM_CASES_TAC `is_kernel_page_address vpa` THENL
   [MP_TAC
      (SPECL
         [`s : state`;
          `s' : state`;
          `pd : page_directory`;
          `vr : virtual_region`;
          `vpa : virtual_page_address`]
         remove_mapping_h_translate_kernel_page_cr3) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    option_cases_tac `translate_page s (cr3 s) vpa` THENL
    [DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC [case_option_def];
     ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN `ppa : physical_page_address` ASSUME_TAC) THEN
    ASM_REWRITE_TAC [case_option_def] THEN
    MP_TAC
      (SPECL
         [`s : state`;
          `s' : state`;
          `pd : page_directory`;
          `vr : virtual_region`;
          `ppa : physical_page_address`]
         remove_mapping_h_is_environment) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    ASM_CASES_TAC `is_environment (status s ppa)` THENL
    [ASM_REWRITE_TAC [case_option_def] THEN
     SUBGOAL_THEN
       `?d.
          status s ppa = Environment d /\
          status s' ppa = Environment d` STRIP_ASSUME_TAC THENL
     [POP_ASSUM MP_TAC THEN
      page_cases_tac `status s ppa` THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC
        [is_environment_def; dest_environment_def;
         is_normal_def; dest_normal_def;
         is_page_table_def; dest_page_table_def;
         is_page_directory_def; dest_page_directory_def;
         is_some_def; option_distinct; option_inj] THEN
      REWRITE_TAC [page_inj; UNWIND_THM1] THEN
      MP_TAC
        (SPECL
           [`s : state`;
            `s' : state`;
            `pd : page_directory`;
            `vr : virtual_region`;
            `ppa : physical_page_address`]
           remove_mapping_h_dest_environment) THEN
      ASM_REWRITE_TAC [dest_environment_def] THEN
      page_cases_tac `status s' ppa` THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC
        [is_environment_def; dest_environment_def;
         is_normal_def; dest_normal_def;
         is_page_table_def; dest_page_table_def;
         is_page_directory_def; dest_page_directory_def;
         is_some_def; option_distinct; option_inj] THEN
      DISCH_THEN SUBST1_TAC THEN
      REFL_TAC;
      ALL_TAC] THEN
     ASM_REWRITE_TAC [dest_environment_or_normal_def; case_option_def] THEN
     AP_TERM_TAC THEN
     AP_TERM_TAC THEN
     MATCH_MP_TAC EXTENSION_IMP THEN
     X_GEN_TAC `vpa' : virtual_page_address` THEN
     ASM_REWRITE_TAC [IN_ELIM] THEN
     AP_THM_TAC THEN
     AP_TERM_TAC THEN
     ASM_CASES_TAC `is_kernel_page_address vpa'` THENL
     [MP_TAC
        (SPECL
           [`s : state`;
            `s' : state`;
            `pd : page_directory`;
            `vr : virtual_region`;
            `vpa' : virtual_page_address`]
           remove_mapping_h_translate_kernel_page_cr3) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      option_cases_tac `translate_page s (cr3 s) vpa'` THENL
      [DISCH_THEN SUBST1_TAC THEN
       REWRITE_TAC [case_option_def];
       ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN `ppa' : physical_page_address` ASSUME_TAC) THEN
      ASM_REWRITE_TAC [case_option_def] THEN
      MP_TAC
        (SPECL
           [`s : state`;
            `s' : state`;
            `pd : page_directory`;
            `vr : virtual_region`;
            `ppa' : physical_page_address`]
           remove_mapping_h_is_environment) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      REFL_TAC;
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `NONE : physical_page_address option` THEN
      CONJ_TAC THENL
      [option_cases_tac `translate_page s (cr3 s) vpa'` THENL
       [DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC [case_option_def];
        ALL_TAC] THEN
       DISCH_THEN (X_CHOOSE_THEN `ppa' : physical_page_address` ASSUME_TAC) THEN
       ASM_REWRITE_TAC [case_option_def] THEN
       MP_TAC
         (SPECL
            [`s : state`;
             `cr3 s`;
             `vpa' : virtual_page_address`;
             `ppa' : physical_page_address`]
            environment_only_kernel_addresses) THEN
       ASM_REWRITE_TAC [] THEN
       DISCH_THEN (SUBST1_TAC o EQF_INTRO) THEN
       REWRITE_TAC [];
       option_cases_tac `translate_page s' (cr3 s') vpa'` THENL
       [DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC [case_option_def];
        ALL_TAC] THEN
       DISCH_THEN (X_CHOOSE_THEN `ppa' : physical_page_address` ASSUME_TAC) THEN
       ASM_REWRITE_TAC [case_option_def] THEN
       MP_TAC
         (SPECL
            [`s' : state`;
             `cr3 s'`;
             `vpa' : virtual_page_address`;
             `ppa' : physical_page_address`]
            environment_only_kernel_addresses) THEN
       ASM_REWRITE_TAC [] THEN
       DISCH_THEN (SUBST1_TAC o EQF_INTRO) THEN
      REWRITE_TAC []]];
     ASM_REWRITE_TAC [case_option_def]];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `NONE : (page_data # virtual_page_address set) option` THEN
    CONJ_TAC THENL
     [option_cases_tac `translate_page s (cr3 s) vpa` THENL
      [DISCH_THEN SUBST1_TAC THEN
       REWRITE_TAC [case_option_def];
       ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN `ppa : physical_page_address` ASSUME_TAC) THEN
      ASM_REWRITE_TAC [case_option_def] THEN
      MP_TAC
        (SPECL
           [`s : state`;
            `cr3 s`;
            `vpa : virtual_page_address`;
            `ppa : physical_page_address`]
           environment_only_kernel_addresses) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (SUBST1_TAC o EQF_INTRO) THEN
      REWRITE_TAC [case_option_def];
      option_cases_tac `translate_page s' (cr3 s') vpa` THENL
      [DISCH_THEN SUBST1_TAC THEN
       REWRITE_TAC [case_option_def];
       ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN `ppa : physical_page_address` ASSUME_TAC) THEN
      ASM_REWRITE_TAC [case_option_def] THEN
      MP_TAC
        (SPECL
           [`s' : state`;
            `cr3 s'`;
            `vpa : virtual_page_address`;
            `ppa : physical_page_address`]
           environment_only_kernel_addresses) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (SUBST1_TAC o EQF_INTRO) THEN
      REWRITE_TAC [case_option_def]]]);;

let local_respect_add_kernel_mapping_h_view_e = prove
  (`!s s' pr vr.
      wellformed s /\
      wellformed s' /\
      add_kernel_mapping_h pr vr s s' ==>
      view EDomain s = view EDomain s'`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC
     [view_def; view_inj; mk_observable_pages_e_def;
      translate_to_observable_pages_def] THEN
   AP_TERM_TAC THEN
   ABS_TAC THEN
   ASM_CASES_TAC `member_virtual_region vpa vr` THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `NONE : (page_data # virtual_page_address set) option` THEN
    CONJ_TAC THENL
    [SUBGOAL_THEN `is_kernel_page_address vpa` ASSUME_TAC THENL
     [MATCH_MP_TAC is_kernel_region THEN
      EXISTS_TAC `vr : virtual_region` THEN
      ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC add_kernel_mapping_h_is_kernel_region THEN
      EXISTS_TAC `s : state` THEN
      EXISTS_TAC `s' : state` THEN
      EXISTS_TAC `pr : physical_region` THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
     option_cases_tac `translate_page s (cr3 s) vpa` THENL
     [STRIP_TAC THEN
      ASM_REWRITE_TAC [case_option_def];
      ALL_TAC] THEN
     DISCH_THEN (X_CHOOSE_THEN `ppa : physical_page_address` ASSUME_TAC) THEN
     ASM_REWRITE_TAC [case_option_def] THEN
     SUBGOAL_THEN `~is_environment (status s ppa)`
       (fun th -> REWRITE_TAC [th; case_option_def]) THEN
     REWRITE_TAC [GSYM is_environment_page_def] THEN
     MATCH_MP_TAC add_kernel_mapping_h_mapped_wasnt_environment THEN
     EXISTS_TAC `s' : state` THEN
     EXISTS_TAC `pr : physical_region` THEN
     EXISTS_TAC `vr : virtual_region` THEN
     EXISTS_TAC `vpa : virtual_page_address` THEN
     ASM_REWRITE_TAC [] THEN
     MP_TAC
       (SPECL
          [`s : state`;
           `vpa : virtual_page_address`]
          cr3_contains_reference) THEN
     ASM_REWRITE_TAC [] THEN
     MATCH_ACCEPT_TAC EQ_SYM;
     MATCH_MP_TAC EQ_SYM THEN
     MP_TAC
       (SPECL
          [`s : state`;
           `s' : state`;
           `pr : physical_region`;
           `vr : virtual_region`;
           `vpa : virtual_page_address`]
          add_kernel_mapping_h_translate_mapped_page_cr3) THEN
     ASM_REWRITE_TAC [] THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC [case_option_def] THEN
     SUBGOAL_THEN `~is_environment (status s' ppa)`
       (fun th -> REWRITE_TAC [th; case_option_def]) THEN
     MP_TAC
       (SPECL
          [`s : state`;
           `s' : state`;
           `pr : physical_region`;
           `vr : virtual_region`;
           `ppa : physical_page_address`]
          add_kernel_mapping_h_is_environment) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (SUBST1_TAC o SYM) THEN
     SUBGOAL_THEN `is_normal_page s ppa` MP_TAC THENL
     [MATCH_MP_TAC add_kernel_mapping_h_mapped_is_normal_page THEN
      EXISTS_TAC `s' : state` THEN
      EXISTS_TAC `pr : physical_region` THEN
      EXISTS_TAC `vr : virtual_region` THEN
      ASM_REWRITE_TAC [];
      POP_ASSUM_LIST (K ALL_TAC) THEN
      REWRITE_TAC [is_normal_page_def] THEN
      page_cases_tac `status s ppa` THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC
        [is_normal_def; is_environment_def; dest_normal_def;
         dest_environment_def; is_some_def]]];
    MP_TAC
      (SPECL
         [`s : state`;
          `s' : state`;
          `pr : physical_region`;
          `vr : virtual_region`;
          `vpa : virtual_page_address`]
         add_kernel_mapping_h_translate_page_cr3) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    option_cases_tac `translate_page s (cr3 s) vpa` THENL
    [STRIP_TAC THEN
     ASM_REWRITE_TAC [case_option_def];
     ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN `ppa : physical_page_address` ASSUME_TAC) THEN
    ASM_REWRITE_TAC [case_option_def] THEN
    MP_TAC
      (SPECL
         [`s : state`;
          `s' : state`;
          `pr : physical_region`;
          `vr : virtual_region`;
          `ppa : physical_page_address`]
         add_kernel_mapping_h_is_environment) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    ASM_CASES_TAC `is_environment (status s ppa)` THENL
    [ASM_REWRITE_TAC [case_option_def] THEN
     MP_TAC
       (SPECL
          [`s : state`;
           `s' : state`;
           `pr : physical_region`;
           `vr : virtual_region`;
           `ppa : physical_page_address`]
          add_kernel_mapping_h_dest_environment_or_normal) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (SUBST1_TAC o SYM) THEN
     AP_THM_TAC THEN
     AP_TERM_TAC THEN
     ABS_TAC THEN
     AP_TERM_TAC THEN
     AP_TERM_TAC THEN
     MATCH_MP_TAC EXTENSION_IMP THEN
     X_GEN_TAC `vpa' : virtual_page_address` THEN
     REWRITE_TAC [IN_ELIM] THEN
     AP_THM_TAC THEN
     AP_TERM_TAC THEN
     ASM_CASES_TAC `member_virtual_region vpa' vr` THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `NONE : physical_page_address option` THEN
      CONJ_TAC THENL
      [SUBGOAL_THEN `is_kernel_page_address vpa'` ASSUME_TAC THENL
       [MATCH_MP_TAC is_kernel_region THEN
        EXISTS_TAC `vr : virtual_region` THEN
        ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC add_kernel_mapping_h_is_kernel_region THEN
        EXISTS_TAC `s : state` THEN
        EXISTS_TAC `s' : state` THEN
        EXISTS_TAC `pr : physical_region` THEN
        FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
       option_cases_tac `translate_page s (cr3 s) vpa'` THENL
       [STRIP_TAC THEN
        ASM_REWRITE_TAC [case_option_def];
        ALL_TAC] THEN
       DISCH_THEN (X_CHOOSE_THEN `ppa' : physical_page_address` ASSUME_TAC) THEN
       ASM_REWRITE_TAC [case_option_def] THEN
       SUBGOAL_THEN `~is_environment (status s ppa')`
         (fun th -> REWRITE_TAC [th; case_option_def]) THEN
       REWRITE_TAC [GSYM is_environment_page_def] THEN
       MATCH_MP_TAC add_kernel_mapping_h_mapped_wasnt_environment THEN
       EXISTS_TAC `s' : state` THEN
       EXISTS_TAC `pr : physical_region` THEN
       EXISTS_TAC `vr : virtual_region` THEN
       EXISTS_TAC `vpa' : virtual_page_address` THEN
       ASM_REWRITE_TAC [] THEN
       MP_TAC
         (SPECL
            [`s : state`;
             `vpa' : virtual_page_address`]
            cr3_contains_reference) THEN
       ASM_REWRITE_TAC [] THEN
       MATCH_ACCEPT_TAC EQ_SYM;
       MATCH_MP_TAC EQ_SYM THEN
       MP_TAC
         (SPECL
            [`s : state`;
             `s' : state`;
             `pr : physical_region`;
             `vr : virtual_region`;
             `vpa' : virtual_page_address`]
            add_kernel_mapping_h_translate_mapped_page_cr3) THEN
       ASM_REWRITE_TAC [] THEN
       STRIP_TAC THEN
       ASM_REWRITE_TAC [case_option_def] THEN
       SUBGOAL_THEN `~is_environment (status s' ppa')`
         (fun th -> REWRITE_TAC [th; case_option_def]) THEN
       MP_TAC
         (SPECL
            [`s : state`;
             `s' : state`;
             `pr : physical_region`;
             `vr : virtual_region`;
             `ppa' : physical_page_address`]
            add_kernel_mapping_h_is_environment) THEN
       ASM_REWRITE_TAC [] THEN
       DISCH_THEN (SUBST1_TAC o SYM) THEN
       SUBGOAL_THEN `is_normal_page s ppa'` MP_TAC THENL
       [MATCH_MP_TAC add_kernel_mapping_h_mapped_is_normal_page THEN
        EXISTS_TAC `s' : state` THEN
        EXISTS_TAC `pr : physical_region` THEN
        EXISTS_TAC `vr : virtual_region` THEN
        ASM_REWRITE_TAC [];
        POP_ASSUM_LIST (K ALL_TAC) THEN
        REWRITE_TAC [is_normal_page_def] THEN
        page_cases_tac `status s ppa'` THEN
        STRIP_TAC THEN
        ASM_REWRITE_TAC
          [is_normal_def; is_environment_def; dest_normal_def;
           dest_environment_def; is_some_def]]];
      MP_TAC
        (SPECL
           [`s : state`;
            `s' : state`;
            `pr : physical_region`;
            `vr : virtual_region`;
            `vpa' : virtual_page_address`]
           add_kernel_mapping_h_translate_page_cr3) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      AP_THM_TAC THEN
      AP_TERM_TAC THEN
      ABS_TAC THEN
      AP_THM_TAC THEN
      AP_THM_TAC THEN
      AP_TERM_TAC THEN
      MATCH_MP_TAC add_kernel_mapping_h_is_environment THEN
      EXISTS_TAC `pr : physical_region` THEN
      EXISTS_TAC `vr : virtual_region` THEN
      ASM_REWRITE_TAC []];
     ASM_REWRITE_TAC [case_option_def]]]);;

let local_respect_execute_h_view_e = prove
  (`!s s' pd.
      wellformed s /\ wellformed s' /\ execute_h pd s s' ==>
      view EDomain s = view EDomain s'`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC
     [view_def; view_inj; mk_observable_pages_e_def;
      translate_to_observable_pages_def] THEN
   AP_TERM_TAC THEN
   ABS_TAC THEN
   ASM_CASES_TAC `is_kernel_page_address vpa` THENL
   [MP_TAC (SPEC `s : state` cr3_is_page_directory) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN
    MP_TAC (SPECL [`s : state`; `cr3 s`; `vpa : virtual_page_address`]
              page_directories_contain_reference) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC (SPEC `s' : state` cr3_is_page_directory) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN
    MP_TAC (SPECL [`s' : state`; `cr3 s'`; `vpa : virtual_page_address`]
              page_directories_contain_reference) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    POP_ASSUM MP_TAC THEN
    MP_TAC (SPECL [`s : state`; `s' : state`; `pd : page_directory`]
              execute_h_status) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]) THEN
    STRIP_TAC THEN
    MP_TAC (SPECL [`s : state`; `s' : state`; `pd : page_directory`]
              execute_h_translate_page) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]) THEN
    MP_TAC (SPECL [`s : state`; `s' : state`; `pd : page_directory`]
              execute_h_reference) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]) THEN
    option_cases_tac `translate_page s (reference s) vpa` THENL
    [STRIP_TAC THEN
     ASM_REWRITE_TAC [case_option_def];
     ALL_TAC] THEN
    DISCH_THEN
      (X_CHOOSE_THEN `ppa : physical_page_address` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC [case_option_def] THEN
    ASM_CASES_TAC `is_environment (status s ppa)` THENL
    [ASM_REWRITE_TAC [case_option_def] THEN
     AP_THM_TAC THEN
     AP_TERM_TAC THEN
     ABS_TAC THEN
     AP_TERM_TAC THEN
     AP_TERM_TAC THEN
     REWRITE_TAC [EXTENSION] THEN
     X_GEN_TAC `vpa' : virtual_page_address` THEN
     REWRITE_TAC [IN_ELIM] THEN
     ASM_CASES_TAC `is_kernel_page_address vpa'` THENL
     [MP_TAC (SPECL [`s : state`; `cr3 s`; `vpa' : virtual_page_address`]
                page_directories_contain_reference) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
      MP_TAC (SPECL [`s : state`; `cr3 s'`; `vpa' : virtual_page_address`]
                page_directories_contain_reference) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (fun th -> REWRITE_TAC [th]);
      AP_THM_TAC THEN
      AP_TERM_TAC THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `NONE : physical_page_address option` THEN
      CONJ_TAC THENL
      [option_cases_tac `translate_page s (cr3 s) vpa'` THENL
       [STRIP_TAC THEN
        ASM_REWRITE_TAC [case_option_def];
        ALL_TAC] THEN
       DISCH_THEN (X_CHOOSE_THEN `ppa' : physical_page_address` ASSUME_TAC) THEN
       ASM_REWRITE_TAC [case_option_def] THEN
       COND_CASES_TAC THENL
       [REWRITE_TAC [option_distinct] THEN
        UNDISCH_TAC `~is_kernel_page_address vpa'` THEN
        REWRITE_TAC [] THEN
        MATCH_MP_TAC environment_only_kernel_addresses THEN
        EXISTS_TAC `s : state` THEN
        EXISTS_TAC `cr3 s` THEN
        EXISTS_TAC `ppa' : physical_page_address` THEN
        ASM_REWRITE_TAC [];
        REFL_TAC];
       option_cases_tac `translate_page s (cr3 s') vpa'` THENL
       [STRIP_TAC THEN
        ASM_REWRITE_TAC [case_option_def];
        ALL_TAC] THEN
       DISCH_THEN (X_CHOOSE_THEN `ppa' : physical_page_address` ASSUME_TAC) THEN
       ASM_REWRITE_TAC [case_option_def] THEN
       COND_CASES_TAC THENL
       [REWRITE_TAC [option_distinct] THEN
        UNDISCH_TAC `~is_kernel_page_address vpa'` THEN
        REWRITE_TAC [] THEN
        MATCH_MP_TAC environment_only_kernel_addresses THEN
        EXISTS_TAC `s : state` THEN
        EXISTS_TAC `cr3 s'` THEN
        EXISTS_TAC `ppa' : physical_page_address` THEN
        ASM_REWRITE_TAC [];
        REFL_TAC]]];
     ASM_REWRITE_TAC [case_option_def]];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `NONE : (page_data # virtual_page_address set) option` THEN
    CONJ_TAC THENL
    [option_cases_tac `translate_page s (cr3 s) vpa` THENL
     [STRIP_TAC THEN
      ASM_REWRITE_TAC [case_option_def];
      ALL_TAC] THEN
     DISCH_THEN (X_CHOOSE_THEN `ppa : physical_page_address` ASSUME_TAC) THEN
     ASM_REWRITE_TAC [case_option_def] THEN
     COND_CASES_TAC THENL
     [SUBGOAL_THEN `F` CONTR_TAC THEN
      UNDISCH_TAC `~is_kernel_page_address vpa` THEN
      REWRITE_TAC [] THEN
      MATCH_MP_TAC environment_only_kernel_addresses THEN
      EXISTS_TAC `s : state` THEN
      EXISTS_TAC `cr3 s` THEN
      EXISTS_TAC `ppa : physical_page_address` THEN
      ASM_REWRITE_TAC [];
      REWRITE_TAC [case_option_def]];
     option_cases_tac `translate_page s' (cr3 s') vpa` THENL
     [STRIP_TAC THEN
      ASM_REWRITE_TAC [case_option_def];
      ALL_TAC] THEN
     DISCH_THEN (X_CHOOSE_THEN `ppa : physical_page_address` ASSUME_TAC) THEN
     ASM_REWRITE_TAC [case_option_def] THEN
     COND_CASES_TAC THENL
     [SUBGOAL_THEN `F` CONTR_TAC THEN
      UNDISCH_TAC `~is_kernel_page_address vpa` THEN
      REWRITE_TAC [] THEN
      MATCH_MP_TAC environment_only_kernel_addresses THEN
      EXISTS_TAC `s' : state` THEN
      EXISTS_TAC `cr3 s'` THEN
      EXISTS_TAC `ppa : physical_page_address` THEN
      ASM_REWRITE_TAC [];
      REWRITE_TAC [case_option_def]]]]);;

let local_respect_write_k_view_e = prove
  (`!s s' va b.
      write_k va b s s' ==>
      view EDomain s = view EDomain s'`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC
     [view_def; view_inj; mk_observable_pages_e_def;
      translate_to_observable_pages_def] THEN
   AP_TERM_TAC THEN
   ABS_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_k_translate_page_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]) THEN
   option_cases_tac `translate_page s (cr3 s) vpa` THENL
   [STRIP_TAC THEN
    ASM_REWRITE_TAC [case_option_def];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `ppa : physical_page_address` ASSUME_TAC) THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_k_is_environment) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]) THEN
   ASM_CASES_TAC `is_environment (status s ppa)` THENL
   [ASM_REWRITE_TAC [case_option_def] THEN
    AP_TERM_TAC THEN
    AP_TERM_TAC THEN
    MATCH_MP_TAC write_k_status THEN
    EXISTS_TAC `va : virtual_address` THEN
    EXISTS_TAC `b : byte` THEN
    ASM_REWRITE_TAC [] THEN
    DISJ1_TAC THEN
    POP_ASSUM MP_TAC THEN
    page_cases_tac `status s ppa` THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC
      [is_normal_def; is_environment_def; is_some_def;
       dest_normal_def; dest_environment_def];
    ASM_REWRITE_TAC [case_option_def]]);;

let local_respect_write_k_view_h = prove
  (`!s s' va b.
      write_k va b s s' ==>
      view HDomain s = view HDomain s'`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC
     [view_def; view_inj; mk_current_page_directory_h_def;
      mk_region_handles_h_def; mk_reference_page_directory_h_def] THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_k_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_k_reference) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_k_regions) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   X_GEN_TAC `ppa : physical_page_address` THEN
   REWRITE_TAC [mk_pages_h_def; LET_DEF; LET_END_DEF] THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`;
             `ppa : physical_page_address`]
      write_k_status) THEN
   ASM_REWRITE_TAC [] THEN
   page_cases_tac `status s ppa` THEN
   STRIP_TAC THEN
   page_cases_tac `status s' ppa` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_normal_def; is_some_def;
      dest_normal_def; case_option_def; page_distinct;
      page_inj; option_distinct; option_inj]);;

let local_respect_write_u_view_e = prove
  (`!s s' va b.
      write_u va b s s' ==>
      view EDomain s = view EDomain s'`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC
     [view_def; view_inj; mk_observable_pages_e_def;
      translate_to_observable_pages_def] THEN
   AP_TERM_TAC THEN
   ABS_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_u_translate_page_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]) THEN
   option_cases_tac `translate_page s (cr3 s) vpa` THENL
   [STRIP_TAC THEN
    ASM_REWRITE_TAC [case_option_def];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `ppa : physical_page_address` ASSUME_TAC) THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_u_is_environment) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]) THEN
   ASM_CASES_TAC `is_environment (status s ppa)` THENL
   [ASM_REWRITE_TAC [case_option_def] THEN
    AP_TERM_TAC THEN
    AP_TERM_TAC THEN
    MATCH_MP_TAC write_u_status THEN
    EXISTS_TAC `va : virtual_address` THEN
    EXISTS_TAC `b : byte` THEN
    ASM_REWRITE_TAC [] THEN
    DISJ1_TAC THEN
    POP_ASSUM MP_TAC THEN
    page_cases_tac `status s ppa` THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC
      [is_normal_def; is_environment_def; is_some_def;
       dest_normal_def; dest_environment_def];
    ASM_REWRITE_TAC [case_option_def]]);;

let local_respect_write_u_view_h = prove
  (`!s s' va b.
      write_u va b s s' ==>
      view HDomain s = view HDomain s'`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC
     [view_def; view_inj; mk_current_page_directory_h_def;
      mk_region_handles_h_def; mk_reference_page_directory_h_def] THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_u_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_u_reference) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_u_regions) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   X_GEN_TAC `ppa : physical_page_address` THEN
   REWRITE_TAC [mk_pages_h_def; LET_DEF; LET_END_DEF] THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`;
             `ppa : physical_page_address`]
      write_u_status) THEN
   ASM_REWRITE_TAC [] THEN
   page_cases_tac `status s ppa` THEN
   STRIP_TAC THEN
   page_cases_tac `status s' ppa` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_normal_def; is_some_def;
      dest_normal_def; case_option_def; page_distinct;
      page_inj; option_distinct; option_inj]);;

let local_respect = prove
  (`!s s' a u.
      ~interferes (domain a) u /\
      action a s s' ==>
      view_equiv u s s'`,
   REWRITE_TAC [action_def; view_equiv_def] THEN
   GEN_TAC THEN
   GEN_TAC THEN
   MATCH_MP_TAC action_induct THEN
   REPEAT CONJ_TAC THEN
   REPEAT GEN_TAC THEN
   SPEC_TAC (`u : domain`, `u : domain`) THEN
   MATCH_MP_TAC domain_induct THEN
   REPEAT CONJ_TAC THEN
   REWRITE_TAC
     [interferes_def; domain_def; action_spec_def; domain_distinct] THENL
   [(* write_e view_u *)
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC local_respect_write_e_view_u THEN
    EXISTS_TAC `va : virtual_address` THEN
    EXISTS_TAC `b : byte` THEN
    ASM_REWRITE_TAC [];

    (* derive_region_h view_e *)
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC local_respect_derive_region_h_view_e THEN
    EXISTS_TAC `pr : physical_region` THEN
    EXISTS_TAC `ppa : physical_page_address` THEN
    EXISTS_TAC `l : region_length` THEN
    ASM_REWRITE_TAC [];

    (* allocate_page_directory_h view_e *)
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC local_respect_allocate_page_directory_h_view_e THEN
    EXISTS_TAC `ppa : physical_page_address` THEN
    ASM_REWRITE_TAC [];

    (* free_page_directory_h view_e *)
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC local_respect_free_page_directory_h_view_e THEN
    EXISTS_TAC `pd : page_directory` THEN
    ASM_REWRITE_TAC [];

    (* add_mapping_h view_e *)
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC local_respect_add_mapping_h_view_e THEN
    EXISTS_TAC `pd : page_directory` THEN
    EXISTS_TAC `pts : page_table list` THEN
    EXISTS_TAC `pr : physical_region` THEN
    EXISTS_TAC `vr : virtual_region` THEN
    ASM_REWRITE_TAC [];

    (* remove_mapping_h view_e *)
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC local_respect_remove_mapping_h_view_e THEN
    EXISTS_TAC `pd : page_directory` THEN
    EXISTS_TAC `vr : virtual_region` THEN
    ASM_REWRITE_TAC [];

    (* add_kernel_mapping_h view_e *)
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC local_respect_add_kernel_mapping_h_view_e THEN
    EXISTS_TAC `pr : physical_region` THEN
    EXISTS_TAC `vr : virtual_region` THEN
    ASM_REWRITE_TAC [];

    (* execute_h view_e *)
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC local_respect_execute_h_view_e THEN
    EXISTS_TAC `pd : page_directory` THEN
    ASM_REWRITE_TAC [];

    (* write_k view_e *)
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC local_respect_write_k_view_e THEN
    EXISTS_TAC `va : virtual_address` THEN
    EXISTS_TAC `b : byte` THEN
    ASM_REWRITE_TAC [];

    (* write_k view_h *)
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC local_respect_write_k_view_h THEN
    EXISTS_TAC `va : virtual_address` THEN
    EXISTS_TAC `b : byte` THEN
    ASM_REWRITE_TAC [];

    (* write_u view_e *)
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC local_respect_write_u_view_e THEN
    EXISTS_TAC `va : virtual_address` THEN
    EXISTS_TAC `b : byte` THEN
    ASM_REWRITE_TAC [];

    (* write_u view_h *)
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC local_respect_write_u_view_h THEN
    EXISTS_TAC `va : virtual_address` THEN
    EXISTS_TAC `b : byte` THEN
    ASM_REWRITE_TAC []]);;

export_thm local_respect;;

(* Weak step consistency *)

let weak_step_consistency_write_e_view_e = prove
  (`!s s' t t' va b.
      view_equiv EDomain s t /\
      action (WriteE va b) s s' /\
      action (WriteE va b) t t' ==>
      view_equiv EDomain s' t'`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC [view_equiv_def; action_def; action_spec_def] THEN
    STRIP_TAC THEN
    MP_TAC
      (SPECL
         [`va : virtual_address`;
          `b : byte`]
         write_e_view_e) THEN
    STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o SPECL [`s : state`; `s' : state`]) THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`t : state`; `t' : state`]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN SUBST1_TAC THEN
    REFL_TAC);;

(* Unfinished (see comment at top of file)
let weak_step_consistency = prove
  (`!s s' t t' a u.
      view_equiv u s t /\
      view_equiv (domain a) s t /\
      action a s s' /\
      action a t t' ==>
      view_equiv u s' t'`,
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `interferes (domain a) u` THENL
   [REPEAT (POP_ASSUM MP_TAC) THEN
    SPEC_TAC (`u : domain`, `u : domain`) THEN
    MATCH_MP_TAC domain_induct THEN
    REPEAT CONJ_TAC THEN
    SPEC_TAC (`a : action`, `a : action`) THEN
    MATCH_MP_TAC action_induct THEN
    REPEAT CONJ_TAC THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC [interferes_def; domain_def; domain_distinct] THEN
    REPEAT STRIP_TAC THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    REWRITE_TAC [IMP_IMP; GSYM CONJ_ASSOC] THENL
    [MATCH_ACCEPT_TAC weak_step_consistency_write_e_view_e;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC;
     CHEAT_TAC];
    MATCH_MP_TAC view_equiv_trans THEN
    EXISTS_TAC `t : state` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC view_equiv_trans THEN
     EXISTS_TAC `s : state` THEN
     ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC view_equiv_symm THEN
     MATCH_MP_TAC local_respect THEN
     EXISTS_TAC `a : action` THEN
     ASM_REWRITE_TAC [];
     MATCH_MP_TAC local_respect THEN
     EXISTS_TAC `a : action` THEN
     ASM_REWRITE_TAC []]]);;

export_thm weak_step_consistency;;

(* Output consistency *)

let output_consistency = prove
  (`!s s' t t' a.
      view_equiv (domain a) s t /\
      action a s s' /\
      action a t t' ==>
      output a s' = output a t'`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [output_def] THEN
   AP_TERM_TAC THEN
   REWRITE_TAC [GSYM view_equiv_def] THEN
   MATCH_MP_TAC weak_step_consistency THEN
   EXISTS_TAC `s : state` THEN
   EXISTS_TAC `t : state` THEN
   EXISTS_TAC `a : action` THEN
   ASM_REWRITE_TAC []);;

export_thm output_consistency;;
*)

(* ------------------------------------------------------------------------- *)
(* HOL Light theorem names.                                                  *)
(* ------------------------------------------------------------------------- *)

export_theory "h-hol-light-thm";;

export_theory_thm_names "h"
  ["h-def";
   "h-thm"];;
