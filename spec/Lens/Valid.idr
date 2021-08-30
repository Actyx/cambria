module Lens.Valid

import Data.List
import Data.Maybe
import Lens
import Lens.Uninhabited
import Lens.Util
import Map

%default total


make_preserves_validity : (k : Kind) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (Make k) s = Just s' -> transform_value (Make k) v = v' ->
    validate s v = True -> validate s' v' = True
make_preserves_validity KNull _ _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KBoolean) SNull SNull _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KBoolean) SNull SBoolean _ _ _ prf1 _ = rewrite sym prf1 in Refl
make_preserves_validity (KPrimitive KBoolean) SNull SNumber _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KBoolean) SNull SText _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KBoolean) SNull (SArray _ _) _ _ prf _ _ = absurd $ justInjective prf
make_preserves_validity (KPrimitive KBoolean) SNull (SObject _) _ _ prf _ _ = absurd $ justInjective prf
make_preserves_validity (KPrimitive KBoolean) SBoolean _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KBoolean) SNumber _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KBoolean) SText _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KBoolean) (SArray _ _) _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KBoolean) (SObject _) _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KNumber) SNull SNull _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KNumber) SNull SBoolean _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KNumber) SNull SNumber _ _ _ prf1 _ = rewrite sym prf1 in Refl
make_preserves_validity (KPrimitive KNumber) SNull SText _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KNumber) SNull (SArray _ _) _ _ prf _ _ = absurd $ justInjective prf
make_preserves_validity (KPrimitive KNumber) SNull (SObject _) _ _ prf _ _ = absurd $ justInjective prf
make_preserves_validity (KPrimitive KNumber) SBoolean _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KNumber) SNumber _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KNumber) SText _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KNumber) (SArray _ _) _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KNumber) (SObject _) _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KText) SNull SNull _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KText) SNull SBoolean _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KText) SNull SNumber _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KText) SNull SText _ _ _ prf1 _ = rewrite sym prf1 in Refl
make_preserves_validity (KPrimitive KText) SNull (SArray _ _) _ _ prf _ _ = absurd $ justInjective prf
make_preserves_validity (KPrimitive KText) SNull (SObject _) _ _ prf _ _ = absurd $ justInjective prf
make_preserves_validity (KPrimitive KText) SBoolean _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KText) SNumber _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KText) SText _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KText) (SArray _ _) _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KText) (SObject _) _ _ _ Refl _ _ impossible
make_preserves_validity KArray SNull SNull _ _ Refl _ _ impossible
make_preserves_validity KArray SNull SBoolean _ _ Refl _ _ impossible
make_preserves_validity KArray SNull SNumber _ _ Refl _ _ impossible
make_preserves_validity KArray SNull SText _ _ Refl _ _ impossible
make_preserves_validity KArray SNull (SArray False _) _ _ prf _ _ = absurd $ justInjective prf
make_preserves_validity KArray SNull (SArray True _) _ _ _ prf1 _ = rewrite sym prf1 in Refl
make_preserves_validity KArray SNull (SObject _) _ _ prf _ _ = absurd $ justInjective prf
make_preserves_validity KArray SBoolean _ _ _ Refl _ _ impossible
make_preserves_validity KArray SNumber _ _ _ Refl _ _ impossible
make_preserves_validity KArray SText _ _ _ Refl _ _ impossible
make_preserves_validity KArray (SArray _ _) _ _ _ Refl _ _ impossible
make_preserves_validity KArray (SObject _) _ _ _ Refl _ _ impossible
make_preserves_validity KObject SNull SNull _ _ Refl _ _ impossible
make_preserves_validity KObject SNull SBoolean _ _ Refl _ _ impossible
make_preserves_validity KObject SNull SNumber _ _ Refl _ _ impossible
make_preserves_validity KObject SNull SText _ _ Refl _ _ impossible
make_preserves_validity KObject SNull (SArray _ _) _ _ prf _ _ = absurd $ justInjective prf
make_preserves_validity KObject SNull (SObject Empty) _ _ _ prf1 _ = rewrite sym prf1 in Refl
make_preserves_validity KObject SNull (SObject (Update _ _ _)) _ _ prf _ _ = absurd $ justInjective prf
make_preserves_validity KObject SBoolean _ _ _ Refl _ _ impossible
make_preserves_validity KObject SNumber _ _ _ Refl _ _ impossible
make_preserves_validity KObject SText _ _ _ Refl _ _ impossible
make_preserves_validity KObject (SArray _ _) _ _ _ Refl _ _ impossible
make_preserves_validity KObject (SObject _) _ _ _ Refl _ _ impossible

destroy_preserves_validity : (k : Kind) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (Destroy k) s = Just s' -> transform_value (Destroy k) v = v' ->
    validate s v = True -> validate s' v' = True
destroy_preserves_validity KNull _ _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KBoolean) SNull _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KBoolean) SBoolean SNull _ _ Refl prf1 _ = rewrite sym prf1 in Refl
destroy_preserves_validity (KPrimitive KBoolean) SNumber _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KBoolean) SText _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KBoolean) (SArray _ _) _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KBoolean) (SObject _) _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KNumber) SNull _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KNumber) SBoolean _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KNumber) SNumber SNull _ _ Refl prf1 _ = rewrite sym prf1 in Refl
destroy_preserves_validity (KPrimitive KNumber) SText _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KNumber) (SArray _ _) _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KNumber) (SObject _) _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KText) SNull _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KText) SBoolean _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KText) SNumber _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KText) SText SNull _ _ Refl prf1 prf2 = rewrite sym prf1 in Refl
destroy_preserves_validity (KPrimitive KText) (SArray _ _) _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KText) (SObject _) _ _ _ Refl _ _ impossible
destroy_preserves_validity KArray SNull _ _ _ Refl _ _ impossible
destroy_preserves_validity KArray SBoolean _ _ _ Refl _ _ impossible
destroy_preserves_validity KArray SNumber _ _ _ Refl _ _ impossible
destroy_preserves_validity KArray SText _ _ _ Refl _ _ impossible
destroy_preserves_validity KArray (SArray False _) _ _ _ Refl _ _ impossible
destroy_preserves_validity KArray (SArray True SNull) SNull _ _ Refl prf1 _ = rewrite sym prf1 in Refl
destroy_preserves_validity KArray (SArray True SBoolean) _ _ _ Refl _ _ impossible
destroy_preserves_validity KArray (SArray True SNumber) _ _ _ Refl _ _ impossible
destroy_preserves_validity KArray (SArray True SText) _ _ _ Refl _ _ impossible
destroy_preserves_validity KArray (SArray True (SArray _ _)) _ _ _ Refl _ _ impossible
destroy_preserves_validity KArray (SArray True (SObject _)) _ _ _ Refl _ _ impossible
destroy_preserves_validity KArray (SObject _) _ _ _ Refl _ _ impossible
destroy_preserves_validity KObject SNull _ _ _ Refl _ _ impossible
destroy_preserves_validity KObject SBoolean _ _ _ Refl _ _ impossible
destroy_preserves_validity KObject SNumber _ _ _ Refl _ _ impossible
destroy_preserves_validity KObject SText _ _ _ Refl _ _ impossible
destroy_preserves_validity KObject (SArray _ _) _ _ _ Refl _ _ impossible
destroy_preserves_validity KObject (SObject Empty) SNull _ _ Refl prf1 _ = rewrite sym prf1 in Refl
destroy_preserves_validity KObject (SObject (Update _ _ _)) _ _ _ Refl _ _ impossible

add_property_preserves_validity : (k : Key) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (AddProperty k) s = Just s' -> transform_value (AddProperty k) v = v' ->
    validate s v = True -> validate s' v' = True
add_property_preserves_validity _ SNull _ _ _ Refl _ _ impossible
add_property_preserves_validity _ SBoolean _ _ _ Refl _ _ impossible
add_property_preserves_validity _ SNumber _ _ _ Refl _ _ impossible
add_property_preserves_validity _ SText _ _ _ Refl _ _ impossible
add_property_preserves_validity _ (SArray _ _) _ _ _ Refl _ _ impossible
add_property_preserves_validity k (SObject m) s' v v' prf prf1 prf2 with (get k m) proof prf3
    add_property_preserves_validity k (SObject _) _ _ _ prf _ _ | (Just _) = absurd $ prf
    add_property_preserves_validity k (SObject _) _ Null _ _ _ prf2 | Nothing = absurd $ prf2
    add_property_preserves_validity k (SObject _) _ (Primitive _) _ _ _ prf2 | Nothing = absurd $ prf2
    add_property_preserves_validity k (SObject _) _ (Array _) _ _ _ prf2 | Nothing = absurd $ prf2
    add_property_preserves_validity k (SObject sm) s' (Object vm) v' prf prf1 prf2 | Nothing =
        rewrite sym $ justInjective prf in
        rewrite sym prf1 in
        let
            split = and_split (half_keys_eq sm vm) (validate_properties vm sm) prf2
            exist = half_keys_eq_insert sm vm k SNull Null (fst split)
            valid = validate_properties_after_insert vm sm k Null SNull Refl (snd split)
        in rewrite exist in rewrite valid in Refl

remove_property_preserves_validity : (k : Key) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (RemoveProperty k) s = Just s' -> transform_value (RemoveProperty k) v = v' ->
    validate s v = True -> validate s' v' = True
remove_property_preserves_validity _ SNull _ _ _ Refl _ _ impossible
remove_property_preserves_validity _ SBoolean _ _ _ Refl _ _ impossible
remove_property_preserves_validity _ SNumber _ _ _ Refl _ _ impossible
remove_property_preserves_validity _ SText _ _ _ Refl _ _ impossible
remove_property_preserves_validity _ (SArray _ _) _ _ _ Refl _ _ impossible
remove_property_preserves_validity k (SObject m) s' v v' prf prf1 prf2 with (get k m) proof prf3
    remove_property_preserves_validity _ (SObject _) _ _ _ prf _ _ | Nothing = absurd $ prf
    remove_property_preserves_validity _ (SObject _) _ Null _ _ _ prf2 | (Just _) = absurd $ prf2
    remove_property_preserves_validity _ (SObject _) _ (Primitive _) _ _ _ prf2 | (Just _) = absurd $ prf2
    remove_property_preserves_validity _ (SObject _) _ (Array _) _ _ _ prf2 | (Just _) = absurd $ prf2
    remove_property_preserves_validity _ (SObject _) _ (Object _) _ prf _ _ | (Just SBoolean) = absurd $ prf
    remove_property_preserves_validity _ (SObject _) _ (Object _) _ prf _ _ | (Just SNumber) = absurd $ prf
    remove_property_preserves_validity _ (SObject _) _ (Object _) _ prf _ _ | (Just SText) = absurd $ prf
    remove_property_preserves_validity _ (SObject _) _ (Object _) _ prf _ _ | (Just (SArray _ _)) = absurd $ prf
    remove_property_preserves_validity _ (SObject _) _ (Object _) _ prf _ _ | (Just (SObject _)) = absurd $ prf
    remove_property_preserves_validity k (SObject sm) s' (Object vm) v' prf prf1 prf2 | (Just SNull) =
        rewrite sym $ justInjective prf in
        rewrite sym prf1 in
        let
            split = and_split (half_keys_eq sm vm) (validate_properties vm sm) prf2
            exist = half_keys_eq_remove sm vm k (fst split)
            valid = validate_properties_after_remove vm sm k (snd split)
        in rewrite exist in rewrite valid in Refl

rename_property_preserves_validity : (k, k' : Key) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (RenameProperty k k') s = Just s' -> transform_value (RenameProperty k k') v = v' ->
    validate s v = True -> validate s' v' = True
rename_property_preserves_validity _ _ SNull _ _ _ Refl _ _ impossible
rename_property_preserves_validity _ _ SBoolean _ _ _ Refl _ _ impossible
rename_property_preserves_validity _ _ SNumber _ _ _ Refl _ _ impossible
rename_property_preserves_validity _ _ SText _ _ _ Refl _ _ impossible
rename_property_preserves_validity _ _ (SArray _ _) _ _ _ Refl _ _ impossible
rename_property_preserves_validity k k' (SObject sm) s' v v' prf prf1 prf2 with (get k sm, get k' sm) proof prf3
    rename_property_preserves_validity _ _ (SObject _) _ _ _ prf _ _ | (Nothing, _) = absurd $ prf
    rename_property_preserves_validity _ _ (SObject _) _ _ _ prf _ _ | (Just _, Just _) = absurd $ prf
    rename_property_preserves_validity _ _ (SObject _) _ Null _ _ _ prf2 | (Just _, Nothing) = absurd $ prf2
    rename_property_preserves_validity _ _ (SObject _) _ (Primitive _) _ _ _ prf2 | (Just _, Nothing) = absurd $ prf2
    rename_property_preserves_validity _ _ (SObject _) _ (Array _) _ _ _ prf2 | (Just _, Nothing) = absurd $ prf2
    rename_property_preserves_validity k k' (SObject sm) _ (Object vm) _ prf prf1 prf2 | (Just ksm, Nothing) with (get k vm) proof prf4
        rename_property_preserves_validity k k' (SObject sm) _ (Object vm) _ prf prf1 prf2 | (Just ksm, Nothing) | Just kvm =
            rewrite sym $ justInjective prf in
            rewrite sym prf1 in
            let
                split = and_split (half_keys_eq sm vm) (validate_properties vm sm) prf2
                exist' = half_keys_eq_remove sm vm k (fst split)
                exist = half_keys_eq_insert (remove k sm) (remove k vm) k' ksm kvm exist'
                valid'' = still_valid vm sm k kvm ksm prf4 (cong fst prf3) (snd split)
                valid' = validate_properties_after_remove vm sm k (snd split)
                valid = validate_properties_after_insert (remove k vm) (remove k sm) k' kvm ksm valid'' valid'
            in rewrite exist in rewrite valid in Refl
        rename_property_preserves_validity k k' (SObject sm) _ (Object vm) _ prf prf1 prf2 | (Just kv, Nothing) | Nothing =
            let
                split = and_split (half_keys_eq sm vm) (validate_properties vm sm) prf2
                contra' = not_half_keys_eq sm vm k (get_just_contains (cong fst prf3)) (get_nothing_contains prf4)
                contra = trans (sym contra') (fst split)
            in absurd contra

hoist_property_preserves_validity : (h, t : Key) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (HoistProperty h t) s = Just s' -> transform_value (HoistProperty h t) v = v' ->
    validate s v = True -> validate s' v' = True
hoist_property_preserves_validity _ _ SNull _ _ _ Refl _ _ impossible
hoist_property_preserves_validity _ _ SBoolean _ _ _ Refl _ _ impossible
hoist_property_preserves_validity _ _ SNumber _ _ _ Refl _ _ impossible
hoist_property_preserves_validity _ _ SText _ _ _ Refl _ _ impossible
hoist_property_preserves_validity _ _ (SArray _ _) _ _ _ Refl _ _ impossible
hoist_property_preserves_validity h t (SObject sm) s' v v' prf prf1 prf2 with (get h sm, get t sm) proof prf3
    hoist_property_preserves_validity _ _ (SObject _) _ _ _ prf _ _ | (Nothing, _) = absurd $ prf
    hoist_property_preserves_validity _ _ (SObject _) _ _ _ prf _ _ | (Just SNull, _) = absurd $ prf
    hoist_property_preserves_validity _ _ (SObject _) _ _ _ prf _ _ | (Just SBoolean, _) = absurd $ prf
    hoist_property_preserves_validity _ _ (SObject _) _ _ _ prf _ _ | (Just SNumber, _) = absurd $ prf
    hoist_property_preserves_validity _ _ (SObject _) _ _ _ prf _ _ | (Just SText, _) = absurd $ prf
    hoist_property_preserves_validity _ _ (SObject _) _ _ _ prf _ _ | (Just (SArray _ _), _) = absurd $ prf
    hoist_property_preserves_validity _ _ (SObject _) _ _ _ prf _ _ | (Just (SObject _), (Just _)) = absurd $ prf
    hoist_property_preserves_validity h t (SObject sm) s' v v' prf prf1 prf2 | (Just (SObject hsm), Nothing) with (get t hsm) proof prf4
        hoist_property_preserves_validity _ _ (SObject _) _ _ _ prf _ _ | (Just (SObject _), Nothing) | Nothing = absurd $ prf
        hoist_property_preserves_validity _ _ (SObject _) _ Null _ _ _ prf2 | (Just (SObject _), Nothing) | Just _ = absurd prf2
        hoist_property_preserves_validity _ _ (SObject _) _ (Primitive _) _ _ _ prf2 | (Just (SObject _), Nothing) | Just _ = absurd prf2
        hoist_property_preserves_validity _ _ (SObject _) _ (Array _) _ _ _ prf2 | (Just (SObject _), Nothing) | Just _ = absurd prf2
        hoist_property_preserves_validity h t (SObject sm) s' (Object vm) v' prf prf1 prf2 | (Just (SObject hsm), Nothing) | Just ts with (get h vm) proof prf5
            hoist_property_preserves_validity h _ (SObject sm) _ (Object vm) _ _ _prf2 | (Just (SObject _), Nothing) | Just _ | Nothing =
                let
                    split = and_split (half_keys_eq sm vm) (validate_properties vm sm) prf2
                    contra' = not_half_keys_eq sm vm h (get_just_contains (cong fst prf3)) (get_nothing_contains prf5)
                    contra = trans (sym contra') (fst split)
                in absurd contra
            hoist_property_preserves_validity h _ (SObject sm) _ (Object vm) _ _ _ prf2 | (Just (SObject hsm), Nothing) | Just _ | Just Null =
                let
                    split = and_split (half_keys_eq sm vm) (validate_properties vm sm) prf2
                    contra' = invalid_property vm sm h Null (SObject hsm) prf5 (cong fst prf3) Refl
                    contra = trans (sym contra') (snd split)
                in absurd contra
            hoist_property_preserves_validity h _ (SObject sm) _ (Object vm) _ _ _ prf2 | (Just (SObject hsm), Nothing) | Just _ | Just (Primitive hvm) =
                let
                    split = and_split (half_keys_eq sm vm) (validate_properties vm sm) prf2
                    contra' = invalid_property vm sm h (Primitive hvm) (SObject hsm) prf5 (cong fst prf3) Refl
                    contra = trans (sym contra') (snd split)
                in absurd contra
            hoist_property_preserves_validity h _ (SObject sm) _ (Object vm) _ _ _ prf2 | (Just (SObject hsm), Nothing) | Just _ | Just (Array hvm) =
                let
                    split = and_split (half_keys_eq sm vm) (validate_properties vm sm) prf2
                    contra' = invalid_property vm sm h (Array hvm) (SObject hsm) prf5 (cong fst prf3) Refl
                    contra = trans (sym contra') (snd split)
                in absurd contra
            hoist_property_preserves_validity h t (SObject sm) s' (Object vm) v' prf prf1 prf2 | (Just (SObject hsm), Nothing) | Just ts | Just (Object hvm) with (get t hvm) proof prf6
                hoist_property_preserves_validity h t (SObject sm) s' (Object vm) v' prf prf1 prf2 | (Just (SObject hsm), Nothing) | Just ts | Just (Object hvm) | Nothing =
                    let
                        split = and_split (half_keys_eq sm vm) (validate_properties vm sm) prf2
                        contra'' = not_half_keys_eq hsm hvm t (get_just_contains prf4) (get_nothing_contains prf6)
                        contra' = still_invalid vm sm h prf5 (cong fst prf3) (and_join2 contra'')
                        contra = trans (sym contra') (snd split)
                    in absurd contra
                hoist_property_preserves_validity h t (SObject sm) s' (Object vm) v' prf prf1 prf2 | (Just (SObject hsm), Nothing) | Just ts | Just (Object hvm) | (Just tv) =
                    rewrite sym $ justInjective prf in
                    rewrite sym prf1 in
                    let
                        split = and_split (half_keys_eq sm vm) (validate_properties vm sm) prf2
                        exist' = half_keys_eq_insert sm vm t ts tv (fst split)
                        exist = half_keys_eq_insert (insert t ts sm) (insert t tv vm) h (SObject (remove t hsm)) (Object (remove t hvm)) exist'
                        valid''' = still_valid vm sm h (Object hvm) (SObject hsm) prf5 (cong fst prf3) (snd split)
                        split2 = and_split (half_keys_eq hsm hvm) (validate_properties hvm hsm) valid'''
                        valid'' = still_valid hvm hsm t tv ts prf6 prf4 (snd split2)
                        valid' = validate_properties_after_insert vm sm t tv ts valid'' (snd split)
                        exist2 = half_keys_eq_remove hsm hvm t (fst split2)
                        valid2 = validate_properties_after_remove hvm hsm t (snd split2)
                        join = and_join (exist2, valid2)
                        valid = validate_properties_after_insert (insert t tv vm) (insert t ts sm) h (Object (remove t hvm)) (SObject (remove t hsm)) join valid'
                    in rewrite exist in rewrite valid in Refl

plunge_property_preserves_validity : (h, t : Key) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (PlungeProperty h t) s = Just s' -> transform_value (PlungeProperty h t) v = v' ->
    validate s v = True -> validate s' v' = True
plunge_property_preserves_validity _ _ SNull _ _ _ Refl _ _ impossible
plunge_property_preserves_validity _ _ SBoolean _ _ _ Refl _ _ impossible
plunge_property_preserves_validity _ _ SNumber _ _ _ Refl _ _ impossible
plunge_property_preserves_validity _ _ SText _ _ _ Refl _ _ impossible
plunge_property_preserves_validity _ _ (SArray _ _) _ _ _ Refl _ _ impossible
plunge_property_preserves_validity h t (SObject sm) s' v v' prf prf1 prf2 with (get t sm, get h sm, t == h) proof prf3
    plunge_property_preserves_validity _ _ (SObject _) _ _ _ prf _ _ | (Nothing, _, _) = absurd $ prf
    plunge_property_preserves_validity _ _ (SObject _) _ _ _ prf _ _ | (Just _, Nothing, _) = absurd $ prf
    plunge_property_preserves_validity _ _ (SObject _) _ _ _ prf _ _ | (Just _, Just SNull, _) = absurd $ prf
    plunge_property_preserves_validity _ _ (SObject _) _ _ _ prf _ _ | (Just _, Just SBoolean, _) = absurd $ prf
    plunge_property_preserves_validity _ _ (SObject _) _ _ _ prf _ _ | (Just _, Just SNumber, _) = absurd $ prf
    plunge_property_preserves_validity _ _ (SObject _) _ _ _ prf _ _ | (Just _, Just SText, _) = absurd $ prf
    plunge_property_preserves_validity _ _ (SObject _) _ _ _ prf _ _ | (Just _, Just (SArray _ _), _) = absurd $ prf
    plunge_property_preserves_validity _ _ (SObject _) _ _ _ prf _ _ | (Just _, Just (SObject _), True) = absurd $ prf
    plunge_property_preserves_validity h t (SObject sm) s' v v' prf prf1 prf2 | (Just ts, Just (SObject hsm), False) with (get t hsm) proof prf4
        plunge_property_preserves_validity _ _ (SObject _) _ _ _ prf _ _ | (Just _, Just (SObject _), False) | Just _ = absurd $ prf
        plunge_property_preserves_validity _ _ (SObject _) _ Null _ _ _ prf2 | (Just _, Just (SObject _), False) | Nothing = absurd prf2
        plunge_property_preserves_validity _ _ (SObject _) _ (Primitive _) _ _ _ prf2 | (Just _, Just (SObject _), False) | Nothing = absurd prf2
        plunge_property_preserves_validity _ _ (SObject _) _ (Array _) _ _ _ prf2 | (Just _, Just (SObject _), False) | Nothing = absurd prf2
        plunge_property_preserves_validity h t (SObject sm) v (Object vm) v' prf prf1 prf2 | (Just ts, Just (SObject hsm), False) | Nothing with (get h vm, get t vm) proof prf5
            plunge_property_preserves_validity h t (SObject sm) v (Object vm) v' prf prf1 prf2 | (Just ts, Just (SObject hsm), False) | Nothing | (Nothing, _) =
                let
                    split = and_split (half_keys_eq sm vm) (validate_properties vm sm) prf2
                    contra' = not_half_keys_eq sm vm h (get_just_contains (cong (fst . snd) prf3)) (get_nothing_contains (cong fst prf5))
                    contra = trans (sym contra') (fst split)
                in absurd contra
            plunge_property_preserves_validity h t (SObject sm) v (Object vm) v' prf prf1 prf2 | (Just ts, Just (SObject hsm), False) | Nothing | (Just Null, _) =
                let
                    split = and_split (half_keys_eq sm vm) (validate_properties vm sm) prf2
                    contra' = invalid_property vm sm h Null (SObject hsm) (cong fst prf5) (cong (fst . snd) prf3) Refl
                    contra = trans (sym contra') (snd split)
                in absurd contra
            plunge_property_preserves_validity h t (SObject sm) v (Object vm) v' prf prf1 prf2 | (Just ts, Just (SObject hsm), False) | Nothing | (Just (Primitive hvm), _) =
                let
                    split = and_split (half_keys_eq sm vm) (validate_properties vm sm) prf2
                    contra' = invalid_property vm sm h (Primitive hvm) (SObject hsm) (cong fst prf5) (cong (fst . snd) prf3) Refl
                    contra = trans (sym contra') (snd split)
                in absurd contra
            plunge_property_preserves_validity h t (SObject sm) v (Object vm) v' prf prf1 prf2 | (Just ts, Just (SObject hsm), False) | Nothing | (Just (Array hvm), _) =
                let
                    split = and_split (half_keys_eq sm vm) (validate_properties vm sm) prf2
                    contra' = invalid_property vm sm h (Array hvm) (SObject hsm) (cong fst prf5) (cong (fst . snd) prf3) Refl
                    contra = trans (sym contra') (snd split)
                in absurd contra
            plunge_property_preserves_validity h t (SObject sm) v (Object vm) v' prf prf1 prf2 | (Just ts, Just (SObject hsm), False) | Nothing | (Just (Object hvm), Nothing) =
                let
                    split = and_split (half_keys_eq sm vm) (validate_properties vm sm) prf2
                    contra' = not_half_keys_eq sm vm t (get_just_contains (cong fst prf3)) (get_nothing_contains (cong snd prf5))
                    contra = trans (sym contra') (fst split)
                in absurd contra
            plunge_property_preserves_validity h t (SObject sm) v (Object vm) v' prf prf1 prf2 | (Just ts, Just (SObject hsm), False) | Nothing | (Just (Object hvm), Just tv) =
                rewrite sym $ justInjective prf in
                rewrite sym prf1 in
                let
                    split = and_split (half_keys_eq sm vm) (validate_properties vm sm) prf2
                    exist' = half_keys_eq_remove sm vm t (fst split)
                    exist = half_keys_eq_insert (remove t sm) (remove t vm) h (SObject (insert t ts hsm)) (Object (insert t tv hvm)) exist'
                    valid''' = still_valid vm sm h (Object hvm) (SObject hsm) (cong fst prf5) (cong (fst . snd) prf3) (snd split)
                    split2 = and_split (half_keys_eq hsm hvm) (validate_properties hvm hsm) valid'''
                    valid'' = still_valid vm sm t tv ts (cong snd prf5) (cong fst prf3) (snd split)
                    exist2 = half_keys_eq_insert hsm hvm t ts tv (fst split2)
                    valid2 = validate_properties_after_insert hvm hsm t tv ts valid'' (snd split2)
                    join = and_join (exist2, valid2)
                    valid' = validate_properties_after_remove vm sm t (snd split)
                    valid = validate_properties_after_insert (remove t vm) (remove t sm) h (Object (insert t tv hvm)) (SObject (insert t ts hsm)) join valid'
                in rewrite exist in rewrite valid in Refl

wrap_preserves_validity :
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema Wrap s = Just s' -> transform_value Wrap v = v' ->
    validate s v = True -> validate s' v' = True
wrap_preserves_validity _ _ _ _ prf prf1 prf2 =
    rewrite sym $ justInjective prf in rewrite sym prf1 in rewrite prf2 in Refl

head_preserves_validity :
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema Head s = Just s' -> transform_value Head v = v' ->
    validate s v = True -> validate s' v' = True
head_preserves_validity SNull _ _ _ Refl _ _ impossible
head_preserves_validity SBoolean _ _ _ Refl _ _ impossible
head_preserves_validity SNumber _ _ _ Refl _ _ impossible
head_preserves_validity SText _ _ _ Refl _ _ impossible
head_preserves_validity (SArray False _) _ Null _ _ _ Refl impossible
head_preserves_validity (SArray False _) _ (Primitive _) _ _ _ Refl impossible
head_preserves_validity (SArray False _) _ (Array []) _ _ _ Refl impossible
head_preserves_validity (SArray False s) _ (Array (h :: xs)) _ prf prf1 prf2 =
    rewrite sym $ justInjective prf in rewrite sym prf1 in
    let split = and_split (validate s h) (validate (SArray True s) (Array xs)) prf2 in
    rewrite fst split in Refl
head_preserves_validity (SArray False _) _ (Object _) _ _ _ Refl impossible
head_preserves_validity (SArray True _) _ _ _ Refl _ _ impossible
head_preserves_validity (SObject _) _ _ _ Refl _ _ impossible

convert_preserves_validity : (k, k' : PrimitiveKind) -> (m : List (PrimitiveValue, PrimitiveValue)) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (Convert k k' m) s = Just s' -> transform_value (Convert k k' m) v = v' ->
    validate s v = True -> validate s' v' = True
convert_preserves_validity k k' m s s' v v' prf prf1 prf2 with (validate_map k k' m) proof prf3
    convert_preserves_validity KBoolean KBoolean _ _ _ _ _ prf _ _ | False = absurd $ prf
    convert_preserves_validity KBoolean KNumber _ _ _ _ _ prf _ _ | False = absurd $ prf
    convert_preserves_validity KBoolean KText _ _ _ _ _ prf _ _ | False = absurd $ prf
    convert_preserves_validity KNumber KBoolean _ _ _ _ _ prf _ _ | False = absurd $ prf
    convert_preserves_validity KNumber KNumber _ _ _ _ _ prf _ _ | False = absurd $ prf
    convert_preserves_validity KNumber KText _ _ _ _ _ prf _ _ | False = absurd $ prf
    convert_preserves_validity KText KBoolean _ _ _ _ _ prf _ _ | False = absurd $ prf
    convert_preserves_validity KText KNumber _ _ _ _ _ prf _ _ | False = absurd $ prf
    convert_preserves_validity KText KText _ _ _ _ _ prf _ _ | False = absurd $ prf

    convert_preserves_validity KBoolean KBoolean _ SNull _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KBoolean KNumber _ SNull _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KBoolean KText _ SNull _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KBoolean KBoolean _ SNumber _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KBoolean KNumber _ SNumber _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KBoolean KText _ SNumber _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KBoolean KBoolean _ SText _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KBoolean KNumber _ SText _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KBoolean KText _ SText _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KBoolean KBoolean _ (SArray _ _) _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KBoolean KNumber _ (SArray _ _) _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KBoolean KText _ (SArray _ _) _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KBoolean KBoolean _ (SObject _) _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KBoolean KNumber _ (SObject _) _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KBoolean KText _ (SObject _) _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KNumber KBoolean _ SNull _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KNumber KNumber _ SNull _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KNumber KText _ SNull _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KNumber KBoolean _ SBoolean _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KNumber KNumber _ SBoolean _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KNumber KText _ SBoolean _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KNumber KBoolean _ SText _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KNumber KNumber _ SText _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KNumber KText _ SText _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KNumber KBoolean _ (SArray _ _) _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KNumber KNumber _ (SArray _ _) _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KNumber KText _ (SArray _ _) _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KNumber KBoolean _ (SObject _) _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KNumber KNumber _ (SObject _) _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KNumber KText _ (SObject _) _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KText KBoolean _ SNull _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KText KNumber _ SNull _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KText KText _ SNull _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KText KBoolean _ SBoolean _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KText KNumber _ SBoolean _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KText KText _ SBoolean _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KText KBoolean _ SNumber _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KText KNumber _ SNumber _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KText KText _ SNumber _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KText KBoolean _ (SArray _ _) _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KText KNumber _ (SArray _ _) _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KText KText _ (SArray _ _) _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KText KBoolean _ (SObject _) _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KText KNumber _ (SObject _) _ _ _ prf _ _ | True = absurd $ prf
    convert_preserves_validity KText KText _ (SObject _) _ _ _ prf _ _ | True = absurd $ prf

    convert_preserves_validity KBoolean KBoolean _ SBoolean SNull _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KBoolean KNumber _ SBoolean SNull _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KBoolean KText _ SBoolean SNull _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KBoolean KNumber _ SBoolean SBoolean _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KBoolean KText _ SBoolean SBoolean _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KBoolean KBoolean _ SBoolean SNumber _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KBoolean KText _ SBoolean SNumber _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KBoolean KBoolean _ SBoolean SText _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KBoolean KNumber _ SBoolean SText _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KBoolean KBoolean _ SBoolean (SArray _ _) _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KBoolean KNumber _ SBoolean (SArray _ _) _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KBoolean KText _ SBoolean (SArray _ _) _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KBoolean KBoolean _ SBoolean (SObject _) _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KBoolean KNumber _ SBoolean (SObject _) _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KBoolean KText _ SBoolean (SObject _) _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KNumber KBoolean _ SNumber SNull _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KNumber KNumber _ SNumber SNull _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KNumber KText _ SNumber SNull _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KNumber KNumber _ SNumber SBoolean _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KNumber KText _ SNumber SBoolean _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KNumber KBoolean _ SNumber SNumber _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KNumber KText _ SNumber SNumber _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KNumber KBoolean _ SNumber SText _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KNumber KNumber _ SNumber SText _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KNumber KBoolean _ SNumber (SArray _ _) _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KNumber KNumber _ SNumber (SArray _ _) _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KNumber KText _ SNumber (SArray _ _) _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KNumber KBoolean _ SNumber (SObject _) _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KNumber KNumber _ SNumber (SObject _) _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KNumber KText _ SNumber (SObject _) _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KText KBoolean _ SText SNull _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KText KNumber _ SText SNull _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KText KText _ SText SNull _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KText KNumber _ SText SBoolean _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KText KText _ SText SBoolean _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KText KBoolean _ SText SNumber _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KText KText _ SText SNumber _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KText KBoolean _ SText SText _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KText KNumber _ SText SText _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KText KBoolean _ SText (SArray _ _) _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KText KNumber _ SText (SArray _ _) _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KText KText _ SText (SArray _ _) _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KText KBoolean _ SText (SObject _) _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KText KNumber _ SText (SObject _) _ _ prf _ _ | True = absurd $ justInjective prf
    convert_preserves_validity KText KText _ SText (SObject _) _ _ prf _ _ | True = absurd $ justInjective prf

    convert_preserves_validity KBoolean KBoolean _ SBoolean SBoolean Null _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KBoolean KBoolean _ SBoolean SBoolean (Array _) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KBoolean KBoolean _ SBoolean SBoolean (Object _) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KBoolean KBoolean _ SBoolean SBoolean (Primitive (Number _)) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KBoolean KBoolean _ SBoolean SBoolean (Primitive (Text _)) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KBoolean KNumber _ SBoolean SNumber Null _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KBoolean KNumber _ SBoolean SNumber (Array _) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KBoolean KNumber _ SBoolean SNumber (Object _) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KBoolean KNumber _ SBoolean SNumber (Primitive (Number _)) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KBoolean KNumber _ SBoolean SNumber (Primitive (Text _)) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KBoolean KText _ SBoolean SText Null _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KBoolean KText _ SBoolean SText (Array _) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KBoolean KText _ SBoolean SText (Object _) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KBoolean KText _ SBoolean SText (Primitive (Number _)) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KBoolean KText _ SBoolean SText (Primitive (Text _)) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KNumber KBoolean _ SNumber SBoolean Null _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KNumber KBoolean _ SNumber SBoolean (Array _) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KNumber KBoolean _ SNumber SBoolean (Object _) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KNumber KBoolean _ SNumber SBoolean (Primitive (Boolean _)) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KNumber KBoolean _ SNumber SBoolean (Primitive (Text _)) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KNumber KNumber _ SNumber SNumber Null _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KNumber KNumber _ SNumber SNumber (Array _) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KNumber KNumber _ SNumber SNumber (Object _) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KNumber KNumber _ SNumber SNumber (Primitive (Boolean _)) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KNumber KNumber _ SNumber SNumber (Primitive (Text _)) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KNumber KText _ SNumber SText Null _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KNumber KText _ SNumber SText (Array _) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KNumber KText _ SNumber SText (Object _) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KNumber KText _ SNumber SText (Primitive (Boolean _)) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KNumber KText _ SNumber SText (Primitive (Text _)) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KText KBoolean _ SText SBoolean Null _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KText KBoolean _ SText SBoolean (Array _) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KText KBoolean _ SText SBoolean (Object _) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KText KBoolean _ SText SBoolean (Primitive (Boolean _)) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KText KBoolean _ SText SBoolean (Primitive (Number _)) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KText KNumber _ SText SNumber Null _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KText KNumber _ SText SNumber (Array _) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KText KNumber _ SText SNumber (Object _) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KText KNumber _ SText SNumber (Primitive (Boolean _)) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KText KNumber _ SText SNumber (Primitive (Number _)) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KText KText _ SText SText Null _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KText KText _ SText SText (Array _) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KText KText _ SText SText (Object _) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KText KText _ SText SText (Primitive (Boolean _)) _ _ _ prf2 | True = absurd prf2
    convert_preserves_validity KText KText _ SText SText (Primitive (Number _)) _ _ _ prf2 | True = absurd prf2

    convert_preserves_validity KBoolean KBoolean m SBoolean SBoolean (Primitive (Boolean va)) v' prf prf1 prf2 | True with (convert_prim (Boolean va) m) proof prf4
        convert_preserves_validity KBoolean KBoolean _ SBoolean SBoolean (Primitive (Boolean _)) _ _ prf1 _ | True | Nothing =
            rewrite sym prf1 in Refl
        convert_preserves_validity KBoolean KBoolean _ SBoolean SBoolean (Primitive (Boolean _)) _ _ prf1 _ | True | (Just (Boolean _)) =
            rewrite sym prf1 in Refl
        convert_preserves_validity KBoolean KBoolean m SBoolean SBoolean (Primitive (Boolean va)) _ _ _ _ | True | (Just (Number vb)) =
            absurd $ convert_prim_kind m KBoolean KBoolean (Boolean va) (Number vb) prf3 Refl prf4
        convert_preserves_validity KBoolean KBoolean m SBoolean SBoolean (Primitive (Boolean va)) _ _ _ _ | True | (Just (Text vb)) =
            absurd $ convert_prim_kind m KBoolean KBoolean (Boolean va) (Text vb) prf3 Refl prf4
    convert_preserves_validity KBoolean KNumber m SBoolean SNumber (Primitive (Boolean va)) v' prf prf1 prf2 | True with (convert_prim (Boolean va) m) proof prf4
        convert_preserves_validity KBoolean KNumber _ SBoolean SNumber (Primitive (Boolean _)) _ _ prf1 _ | True | Nothing =
            rewrite sym prf1 in Refl
        convert_preserves_validity KBoolean KNumber _ SBoolean SNumber (Primitive (Boolean _)) _ _ prf1 _ | True | (Just (Number _)) =
            rewrite sym prf1 in Refl
        convert_preserves_validity KBoolean KNumber m SBoolean SNumber (Primitive (Boolean va)) _ _ _ _ | True | (Just (Boolean vb)) =
            absurd $ convert_prim_kind m KBoolean KNumber (Boolean va) (Boolean vb) prf3 Refl prf4
        convert_preserves_validity KBoolean KNumber m SBoolean SNumber (Primitive (Boolean va)) _ _ _ _ | True | (Just (Text vb)) =
            absurd $ convert_prim_kind m KBoolean KNumber (Boolean va) (Text vb) prf3 Refl prf4
    convert_preserves_validity KBoolean KText m SBoolean SText (Primitive (Boolean va)) v' prf prf1 prf2 | True with (convert_prim (Boolean va) m) proof prf4
        convert_preserves_validity KBoolean KText _ SBoolean SText (Primitive (Boolean _)) _ _ prf1 _ | True | Nothing =
            rewrite sym prf1 in Refl
        convert_preserves_validity KBoolean KText _ SBoolean SText (Primitive (Boolean _)) _ _ prf1 _ | True | (Just (Text _)) =
            rewrite sym prf1 in Refl
        convert_preserves_validity KBoolean KText m SBoolean SText (Primitive (Boolean va)) _ _ _ _ | True | (Just (Boolean vb)) =
            absurd $ convert_prim_kind m KBoolean KText (Boolean va) (Boolean vb) prf3 Refl prf4
        convert_preserves_validity KBoolean KText m SBoolean SText (Primitive (Boolean va)) _ _ _ _ | True | (Just (Number vb)) =
            absurd $ convert_prim_kind m KBoolean KText (Boolean va) (Number vb) prf3 Refl prf4
    convert_preserves_validity KNumber KBoolean m SNumber SBoolean (Primitive (Number va)) v' prf prf1 prf2 | True with (convert_prim (Number va) m) proof prf4
        convert_preserves_validity KNumber KBoolean _ SNumber SBoolean (Primitive (Number _)) _ _ prf1 _ | True | Nothing =
            rewrite sym prf1 in Refl
        convert_preserves_validity KNumber KBoolean _ SNumber SBoolean (Primitive (Number _)) _ _ prf1 _ | True | (Just (Boolean _)) =
            rewrite sym prf1 in Refl
        convert_preserves_validity KNumber KBoolean m SNumber SBoolean (Primitive (Number va)) _ _ _ _ | True | (Just (Number vb)) =
            absurd $ convert_prim_kind m KNumber KBoolean (Number va) (Number vb) prf3 Refl prf4
        convert_preserves_validity KNumber KBoolean m SNumber SBoolean (Primitive (Number va)) _ _ _ _ | True | (Just (Text vb)) =
            absurd $ convert_prim_kind m KNumber KBoolean (Number va) (Text vb) prf3 Refl prf4
    convert_preserves_validity KNumber KNumber m SNumber SNumber (Primitive (Number va)) v' prf prf1 prf2 | True with (convert_prim (Number va) m) proof prf4
        convert_preserves_validity KNumber KNumber _ SNumber SNumber (Primitive (Number _)) _ _ prf1 _ | True | Nothing =
            rewrite sym prf1 in Refl
        convert_preserves_validity KNumber KNumber _ SNumber SNumber (Primitive (Number _)) _ _ prf1 _ | True | (Just (Number _)) =
            rewrite sym prf1 in Refl
        convert_preserves_validity KNumber KNumber m SNumber SNumber (Primitive (Number va)) _ _ _ _ | True | (Just (Boolean vb)) =
            absurd $ convert_prim_kind m KNumber KNumber (Number va) (Boolean vb) prf3 Refl prf4
        convert_preserves_validity KNumber KNumber m SNumber SNumber (Primitive (Number va)) _ _ _ _ | True | (Just (Text vb)) =
            absurd $ convert_prim_kind m KNumber KNumber (Number va) (Text vb) prf3 Refl prf4
    convert_preserves_validity KNumber KText m SNumber SText (Primitive (Number va)) v' prf prf1 prf2 | True with (convert_prim (Number va) m) proof prf4
        convert_preserves_validity KNumber KText _ SNumber SText (Primitive (Number _)) _ _ prf1 _ | True | Nothing =
            rewrite sym prf1 in Refl
        convert_preserves_validity KNumber KText _ SNumber SText (Primitive (Number _)) _ _ prf1 _ | True | (Just (Text _)) =
            rewrite sym prf1 in Refl
        convert_preserves_validity KNumber KText m SNumber SText (Primitive (Number va)) _ _ _ _ | True | (Just (Boolean vb)) =
            absurd $ convert_prim_kind m KNumber KText (Number va) (Boolean vb) prf3 Refl prf4
        convert_preserves_validity KNumber KText m SNumber SText (Primitive (Number va)) _ _ _ _ | True | (Just (Number vb)) =
            absurd $ convert_prim_kind m KNumber KText (Number va) (Number vb) prf3 Refl prf4
    convert_preserves_validity KText KBoolean m SText SBoolean (Primitive (Text va)) v' prf prf1 prf2 | True with (convert_prim (Text va) m) proof prf4
        convert_preserves_validity KText KBoolean _ SText SBoolean (Primitive (Text _)) _ _ prf1 _ | True | Nothing =
            rewrite sym prf1 in Refl
        convert_preserves_validity KText KBoolean _ SText SBoolean (Primitive (Text _)) _ _ prf1 _ | True | (Just (Boolean _)) =
            rewrite sym prf1 in Refl
        convert_preserves_validity KText KBoolean m SText SBoolean (Primitive (Text va)) _ _ _ _ | True | (Just (Number vb)) =
            absurd $ convert_prim_kind m KText KBoolean (Text va) (Number vb) prf3 Refl prf4
        convert_preserves_validity KText KBoolean m SText SBoolean (Primitive (Text va)) _ _ _ _ | True | (Just (Text vb)) =
            absurd $ convert_prim_kind m KText KBoolean (Text va) (Text vb) prf3 Refl prf4
    convert_preserves_validity KText KNumber m SText SNumber (Primitive (Text va)) v' prf prf1 prf2 | True with (convert_prim (Text va) m) proof prf4
        convert_preserves_validity KText KNumber _ SText SNumber (Primitive (Text _)) _ _ prf1 _ | True | Nothing =
            rewrite sym prf1 in Refl
        convert_preserves_validity KText KNumber _ SText SNumber (Primitive (Text _)) _ _ prf1 _ | True | (Just (Number _)) =
            rewrite sym prf1 in Refl
        convert_preserves_validity KText KNumber m SText SNumber (Primitive (Text va)) _ _ _ _ | True | (Just (Boolean vb)) =
            absurd $ convert_prim_kind m KText KNumber (Text va) (Boolean vb) prf3 Refl prf4
        convert_preserves_validity KText KNumber m SText SNumber (Primitive (Text va)) _ _ _ _ | True | (Just (Text vb)) =
            absurd $ convert_prim_kind m KText KNumber (Text va) (Text vb) prf3 Refl prf4
    convert_preserves_validity KText KText m SText SText (Primitive (Text va)) v' prf prf1 prf2 | True with (convert_prim (Text va) m) proof prf4
        convert_preserves_validity KText KText _ SText SText (Primitive (Text _)) _ _ prf1 _ | True | Nothing =
            rewrite sym prf1 in Refl
        convert_preserves_validity KText KText _ SText SText (Primitive (Text _)) _ _ prf1 _ | True | (Just (Text _)) =
            rewrite sym prf1 in Refl
        convert_preserves_validity KText KText m SText SText (Primitive (Text va)) _ _ _ _ | True | (Just (Boolean vb)) =
            absurd $ convert_prim_kind m KText KText (Text va) (Boolean vb) prf3 Refl prf4
        convert_preserves_validity KText KText m SText SText (Primitive (Text va)) _ _ _ _ | True | (Just (Number vb)) =
            absurd $ convert_prim_kind m KText KText (Text va) (Number vb) prf3 Refl prf4


||| Transforming a valid value must result in a valid value
lens_preserves_validity : (l : Lens) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema l s = Just s' -> transform_value l v = v' ->
    validate s v = True -> validate s' v' = True
lens_preserves_validity (Make k) s s' v v' prf prf1 prf2 =
    make_preserves_validity k s s' v v' prf prf1 prf2
lens_preserves_validity (Destroy k) s s' v v' prf prf1 prf2 =
    destroy_preserves_validity k s s' v v' prf prf1 prf2
lens_preserves_validity (AddProperty k) s s' v v' prf prf1 prf2 =
    add_property_preserves_validity k s s' v v' prf prf1 prf2
lens_preserves_validity (RemoveProperty k) s s' v v' prf prf1 prf2 =
    remove_property_preserves_validity k s s' v v' prf prf1 prf2
lens_preserves_validity (RenameProperty k k') s s' v v' prf prf1 prf2 =
    rename_property_preserves_validity k k' s s' v v' prf prf1 prf2
lens_preserves_validity (HoistProperty h t) s s' v v' prf prf1 prf2 =
    hoist_property_preserves_validity h t s s' v v' prf prf1 prf2
lens_preserves_validity (PlungeProperty h t) s s' v v' prf prf1 prf2 =
    plunge_property_preserves_validity h t s s' v v' prf prf1 prf2
lens_preserves_validity Wrap s s' v v' prf prf1 prf2 =
    wrap_preserves_validity s s' v v' prf prf1 prf2
lens_preserves_validity Head s s' v v' prf prf1 prf2 =
    head_preserves_validity s s' v v' prf prf1 prf2
lens_preserves_validity (LensIn _ _) SNull _ _ _ Refl _ _ impossible
lens_preserves_validity (LensIn _ _) SBoolean _ _ _ Refl _ _ impossible
lens_preserves_validity (LensIn _ _) SNumber _ _ _ Refl _ _ impossible
lens_preserves_validity (LensIn _ _) SText _ _ _ Refl _ _ impossible
lens_preserves_validity (LensIn _ _) (SArray _ _) _ _ _ Refl _ _ impossible
lens_preserves_validity (LensIn _ _) (SObject _) _ Null _ _ _ Refl impossible
lens_preserves_validity (LensIn _ _) (SObject _) _ (Primitive _) _ _ _ Refl impossible
lens_preserves_validity (LensIn _ _) (SObject _) _ (Array _) _ _ _ Refl impossible
lens_preserves_validity (LensIn k l) (SObject sm) s' (Object vm) v' prf prf1 prf2 with (get k sm) proof prf3
    lens_preserves_validity (LensIn k l) (SObject sm) s' (Object vm) v' prf prf1 prf2 | Nothing = absurd $ prf
    lens_preserves_validity (LensIn k l) (SObject sm) s' (Object vm) v' prf prf1 prf2 | Just s2 with (get k vm) proof prf4
        lens_preserves_validity (LensIn k l) (SObject sm) s' (Object vm) v' prf prf1 prf2 | Just s2 | Nothing =
            let split = and_split (half_keys_eq sm vm) (validate_properties vm sm) prf2
                invalid = not_half_keys_eq sm vm k (get_just_contains prf3) (get_nothing_contains prf4)
                contra = trans (sym invalid) (fst split)
            in absurd contra
        lens_preserves_validity (LensIn k l) (SObject sm) s' (Object vm) v' prf prf1 prf2 | Just s2 | Just v2 with (transform_schema l s2) proof prf5
            lens_preserves_validity (LensIn k l) (SObject sm) s' (Object vm) v' prf prf1 prf2 | Just s2 | Just v2 | Nothing = absurd $ prf
            lens_preserves_validity (LensIn k l) (SObject sm) s' (Object vm) v' prf prf1 prf2 | Just s2 | Just v2 | Just s2' =
                rewrite sym $ justInjective prf in
                rewrite sym $ prf1 in
                let split = and_split (half_keys_eq sm vm) (validate_properties vm sm) prf2
                    still = still_valid vm sm k v2 s2 prf4 prf3 (snd split)
                    ind = lens_preserves_validity l s2 s2' v2 (transform_value l v2) prf5 Refl still
                    exist = half_keys_eq_insert sm vm k s2' (transform_value l v2) (fst split)
                    valid = validate_properties_after_insert vm sm k (transform_value l v2) s2' ind (snd split)
                in rewrite exist in valid
lens_preserves_validity (LensMap _) SNull _ _ _ Refl _ _ impossible
lens_preserves_validity (LensMap _) SBoolean _ _ _ Refl _ _ impossible
lens_preserves_validity (LensMap _) SNumber _ _ _ Refl _ _ impossible
lens_preserves_validity (LensMap _) SText _ _ _ Refl _ _ impossible
lens_preserves_validity (LensMap _) (SArray _ _) _ Null _ _ _ Refl impossible
lens_preserves_validity (LensMap _) (SArray _ _) _ (Primitive _) _ _ _ Refl impossible
lens_preserves_validity (LensMap l) (SArray e s2) s' (Array xs) v' prf prf1 prf2 with (transform_schema l s2) proof prf3
    lens_preserves_validity (LensMap _) (SArray _ _) SNull (Array _) _ prf _ _ | (Just _) =
        absurd $ justInjective $ prf
    lens_preserves_validity (LensMap _) (SArray _ _) SBoolean (Array _) _ prf _ _ | (Just _) =
        absurd $ justInjective $ prf
    lens_preserves_validity (LensMap _) (SArray _ _) SNumber (Array _) _ prf _ _ | (Just _) =
        absurd $ justInjective $ prf
    lens_preserves_validity (LensMap _) (SArray _ _) SText (Array _) _ prf _ _ | (Just _) =
        absurd $ justInjective $ prf
    lens_preserves_validity (LensMap _) (SArray _ _) (SObject _) (Array _) _ prf _ _ | (Just _) =
        absurd $ justInjective $ prf
    lens_preserves_validity (LensMap _) (SArray _ _) (SArray _ _) (Array _) Null _ prf1 _ | (Just _) =
        absurd $ prf1
    lens_preserves_validity (LensMap _) (SArray _ _) (SArray _ _) (Array _) (Primitive _) _ prf1 _ | (Just _) =
        absurd $ prf1
    lens_preserves_validity (LensMap _) (SArray _ _) (SArray _ _) (Array _) (Object _) _ prf1 _ | (Just _) =
        absurd $ prf1
    lens_preserves_validity (LensMap _) (SArray _ _) (SArray _ _) (Array []) (Array (_ :: _)) _ prf1 _ | (Just _) =
        absurd $ prf1
    lens_preserves_validity (LensMap _) (SArray _ _) (SArray _ _) (Array (_ :: _)) (Array []) _ prf1 _ | (Just _) =
        absurd $ prf1
    lens_preserves_validity (LensMap _) (SArray _ _) (SArray _ _) (Array []) (Array []) prf _ prf2 | (Just _) =
        rewrite sym $ justInjective $ cong allow_empty $ justInjective prf in
        rewrite prf2 in Refl
    lens_preserves_validity (LensMap l) (SArray e s2) (SArray e' s2') (Array (v2 :: xs)) (Array (v2' :: xs')) prf prf1 prf2 | (Just s2'2) with (validate s2 v2) proof prf4
        lens_preserves_validity (LensMap l) (SArray e s2) (SArray e' s2') (Array (v2 :: xs)) (Array (v2' :: xs')) prf prf1 prf2 | (Just s2'2) | False = absurd $ prf2
        lens_preserves_validity (LensMap l) (SArray e s2) (SArray e' s2') (Array (v2 :: xs)) (Array (v2' :: xs')) prf prf1 prf2 | (Just s2'2) | True =
            let eqs = trans prf3 $ cong sarray $ justInjective prf
                eqv = consInjective $ justInjective $ cong array prf1
                ind = lens_preserves_validity l s2 s2' v2 v2' eqs (fst eqv) prf4
            in rewrite ind in
            let ind = lens_preserves_validity (LensMap l) (SArray True s2) (SArray True s2') (Array xs) (Array xs')
            in ?hhhhhhh


lens_preserves_validity (LensMap _) (SArray _ _) _ (Object _) _ _ _ Refl impossible
lens_preserves_validity (LensMap _) (SObject _) _ _ _ Refl _ _ impossible
lens_preserves_validity (Convert k k' m) s s' v v' prf prf1 prf2 =
    convert_preserves_validity k k' m s s' v v' prf prf1 prf2
