module Lens.Reversible

import Data.Maybe
import Lens
import Lens.Uninhabited
import Lens.Util
import Map

%default total

make_reversible : (k : Kind) ->
    (s : Schema) -> (s' : Schema) ->
    transform_schema (Make k) s = Just s' -> transform_schema (reverse_lens (Make k)) s' = Just s
make_reversible KNull SNull _ Refl impossible
make_reversible KNull SBoolean _ Refl impossible
make_reversible KNull SNumber _ Refl impossible
make_reversible KNull SText _ Refl impossible
make_reversible KNull (SArray _ _) _ Refl impossible
make_reversible KNull (SObject _) _ Refl impossible
make_reversible (KPrimitive KBoolean) SNull SBoolean Refl = Refl
make_reversible (KPrimitive KBoolean) SBoolean _ Refl impossible
make_reversible (KPrimitive KBoolean) SNumber _ Refl impossible
make_reversible (KPrimitive KBoolean) SText _ Refl impossible
make_reversible (KPrimitive KBoolean) (SArray _ _) _ Refl impossible
make_reversible (KPrimitive KBoolean) (SObject _) _ Refl impossible
make_reversible (KPrimitive KNumber) SNull SNumber Refl = Refl
make_reversible (KPrimitive KNumber) SBoolean _ Refl impossible
make_reversible (KPrimitive KNumber) SNumber _ Refl impossible
make_reversible (KPrimitive KNumber) SText _ Refl impossible
make_reversible (KPrimitive KNumber) (SArray _ _) _ Refl impossible
make_reversible (KPrimitive KNumber) (SObject _) _ Refl impossible
make_reversible (KPrimitive KText) SNull SText Refl = Refl
make_reversible (KPrimitive KText) SBoolean _ Refl impossible
make_reversible (KPrimitive KText) SNumber _ Refl impossible
make_reversible (KPrimitive KText) SText _ Refl impossible
make_reversible (KPrimitive KText) (SArray _ _) _ Refl impossible
make_reversible (KPrimitive KText) (SObject _) _ Refl impossible
make_reversible KArray SNull (SArray True SNull) Refl = Refl
make_reversible KArray SBoolean _ Refl impossible
make_reversible KArray SNumber _ Refl impossible
make_reversible KArray SText _ Refl impossible
make_reversible KArray (SArray _ _) _ Refl impossible
make_reversible KArray (SObject _) _ Refl impossible
make_reversible KObject SNull (SObject Empty) Refl = Refl
make_reversible KObject SBoolean _ Refl impossible
make_reversible KObject SNumber _ Refl impossible
make_reversible KObject SText _ Refl impossible
make_reversible KObject (SArray _ _) _ Refl impossible
make_reversible KObject (SObject _) _ Refl impossible

destroy_reversible : (k : Kind) ->
    (s : Schema) -> (s' : Schema) ->
    transform_schema (Destroy k) s = Just s' -> transform_schema (reverse_lens (Destroy k)) s' = Just s
destroy_reversible KNull SNull _ Refl impossible
destroy_reversible KNull SBoolean _ Refl impossible
destroy_reversible KNull SNumber _ Refl impossible
destroy_reversible KNull SText _ Refl impossible
destroy_reversible KNull (SArray _ _) _ Refl impossible
destroy_reversible KNull (SObject _) _ Refl impossible
destroy_reversible (KPrimitive KBoolean) SNull _ Refl impossible
destroy_reversible (KPrimitive KBoolean) SBoolean SNull Refl = Refl
destroy_reversible (KPrimitive KBoolean) SNumber _ Refl impossible
destroy_reversible (KPrimitive KBoolean) SText _ Refl impossible
destroy_reversible (KPrimitive KBoolean) (SArray _ _) _ Refl impossible
destroy_reversible (KPrimitive KBoolean) (SObject _) _ Refl impossible
destroy_reversible (KPrimitive KNumber) SNull _ Refl impossible
destroy_reversible (KPrimitive KNumber) SBoolean _ Refl impossible
destroy_reversible (KPrimitive KNumber) SNumber SNull Refl = Refl
destroy_reversible (KPrimitive KNumber) SText _ Refl impossible
destroy_reversible (KPrimitive KNumber) (SArray _ _) _ Refl impossible
destroy_reversible (KPrimitive KNumber) (SObject _) _ Refl impossible
destroy_reversible (KPrimitive KText) SNull _ Refl impossible
destroy_reversible (KPrimitive KText) SBoolean _ Refl impossible
destroy_reversible (KPrimitive KText) SNumber _ Refl impossible
destroy_reversible (KPrimitive KText) SText SNull Refl = Refl
destroy_reversible (KPrimitive KText) (SArray _ _) _ Refl impossible
destroy_reversible (KPrimitive KText) (SObject _) _ Refl impossible
destroy_reversible KArray SNull _ Refl impossible
destroy_reversible KArray SBoolean _ Refl impossible
destroy_reversible KArray SNumber _ Refl impossible
destroy_reversible KArray SText _ Refl impossible
destroy_reversible KArray (SArray False _) _ Refl impossible
destroy_reversible KArray (SArray True SNull) SNull Refl = Refl
destroy_reversible KArray (SArray True SBoolean) _ Refl impossible
destroy_reversible KArray (SArray True SNumber) _ Refl impossible
destroy_reversible KArray (SArray True SText) _ Refl impossible
destroy_reversible KArray (SArray True (SArray _ _)) _ Refl impossible
destroy_reversible KArray (SArray True (SObject _)) _ Refl impossible
destroy_reversible KArray (SObject _) _ Refl impossible
destroy_reversible KObject SNull _ Refl impossible
destroy_reversible KObject SBoolean _ Refl impossible
destroy_reversible KObject SNumber _ Refl impossible
destroy_reversible KObject SText _ Refl impossible
destroy_reversible KObject (SArray _ _) _ Refl impossible
destroy_reversible KObject (SObject (Update _ _ _)) _ Refl impossible
destroy_reversible KObject (SObject Empty) s' prf =
    rewrite sym $ justInjective prf in Refl

add_property_reversible : (k : Key) ->
    (s : Schema) -> (s' : Schema) ->
    transform_schema (AddProperty k) s = Just s' -> transform_schema (reverse_lens (AddProperty k)) s' = Just s
add_property_reversible _ SNull _ Refl impossible
add_property_reversible _ SBoolean _ Refl impossible
add_property_reversible _ SNumber _ Refl impossible
add_property_reversible _ SText _ Refl impossible
add_property_reversible _ (SArray _ _) _ Refl impossible
add_property_reversible k (SObject m) s' prf with (get k m) proof prf1
    add_property_reversible k (SObject _) _ prf | (Just _) = absurd $ prf
    add_property_reversible k (SObject m) s' prf | Nothing =
        rewrite sym $ justInjective prf in
        rewrite update_eq m k (Just SNull) in
        rewrite update_shadow m k (Just SNull) Nothing in
        rewrite update_same m k Nothing prf1 in Refl

remove_property_reversible : (k : Key) ->
    (s : Schema) -> (s' : Schema) ->
    transform_schema (RemoveProperty k) s = Just s' -> transform_schema (reverse_lens (RemoveProperty k)) s' = Just s
remove_property_reversible _ SNull _ Refl impossible
remove_property_reversible _ SBoolean _ Refl impossible
remove_property_reversible _ SNumber _ Refl impossible
remove_property_reversible _ SText _ Refl impossible
remove_property_reversible _ (SArray _ _) _ Refl impossible
remove_property_reversible k (SObject m) s' prf with (get k m) proof prf1
    remove_property_reversible _ (SObject _) _ prf | Nothing = absurd $ prf
    remove_property_reversible _ (SObject _) _ prf | (Just SBoolean) = absurd $ prf
    remove_property_reversible _ (SObject _) _ prf | (Just SNumber) = absurd $ prf
    remove_property_reversible _ (SObject _) _ prf | (Just SText) = absurd $ prf
    remove_property_reversible _ (SObject _) _ prf | (Just (SArray _ _)) = absurd $ prf
    remove_property_reversible _ (SObject _) _ prf | (Just (SObject _)) = absurd $ prf
    remove_property_reversible k (SObject m) s' prf | (Just SNull) =
        rewrite sym $ justInjective prf in
        rewrite update_eq m k Nothing in
        rewrite update_shadow m k Nothing (Just SNull) in
        rewrite update_same m k (Just SNull) prf1 in Refl

rename_property_reversible : (k, k' : Key) ->
    (s : Schema) -> (s' : Schema) ->
    transform_schema (RenameProperty k k') s = Just s' -> transform_schema (reverse_lens (RenameProperty k k')) s' = Just s
rename_property_reversible _ _ SNull _ Refl impossible
rename_property_reversible _ _ SBoolean _ Refl impossible
rename_property_reversible _ _ SNumber _ Refl impossible
rename_property_reversible _ _ SText _ Refl impossible
rename_property_reversible _ _ (SArray _ _) _ Refl impossible
rename_property_reversible k k' (SObject m) s' prf with (get k m, get k' m) proof prf1
    rename_property_reversible _ _ (SObject _) _ prf | (Nothing, _) = absurd $ prf
    rename_property_reversible _ _ (SObject _) _ prf | (Just _, Just _) = absurd $ prf
    rename_property_reversible k k' (SObject m) s' prf | ((Just x), Nothing) =
        rewrite sym $ justInjective prf in
        rewrite update_eq (update k Nothing m) k' (Just x) in
        let va = cong fst prf1
            vb = cong snd prf1
            not_a_eq_b = get_neq $ tuple_eq prf1 uninhabited
            not_b_eq_a = \p => not_a_eq_b $ sym p in
        rewrite update_permute m k' k (Just x) Nothing not_b_eq_a in
        rewrite ne_key k k' not_a_eq_b in
        rewrite beq_key k in
        rewrite update_permute m k k' Nothing (Just x) not_a_eq_b in
        rewrite update_shadow (update k Nothing m) k' (Just x) Nothing in
        rewrite update_permute m k' k Nothing Nothing not_b_eq_a in
        rewrite update_same m k' Nothing vb in
        rewrite update_shadow m k Nothing (Just x) in
        rewrite update_same m k (Just x) va in Refl

hoist_property_reversible : (h, t : Key) ->
    (s : Schema) -> (s' : Schema) ->
    transform_schema (HoistProperty h t) s = Just s' -> transform_schema (reverse_lens (HoistProperty h t)) s' = Just s
hoist_property_reversible _ _ SNull _ Refl impossible
hoist_property_reversible _ _ SBoolean _ Refl impossible
hoist_property_reversible _ _ SNumber _ Refl impossible
hoist_property_reversible _ _ SText _ Refl impossible
hoist_property_reversible _ _ (SArray _ _) _ Refl impossible
hoist_property_reversible h t (SObject m) s' prf with (get h m, get t m) proof prf1
    hoist_property_reversible _ _ (SObject _) _ prf | (Nothing, _) = absurd $ prf
    hoist_property_reversible _ _ (SObject _) _ prf | (Just SNull, _) = absurd $ prf
    hoist_property_reversible _ _ (SObject _) _ prf | (Just SBoolean, _) = absurd $ prf
    hoist_property_reversible _ _ (SObject _) _ prf | (Just SNumber, _) = absurd $ prf
    hoist_property_reversible _ _ (SObject _) _ prf | (Just SText, _) = absurd $ prf
    hoist_property_reversible _ _ (SObject _) _ prf | (Just (SArray _ _), _) = absurd $ prf
    hoist_property_reversible _ _ (SObject _) _ prf | (Just (SObject _), Just _) = absurd $ prf
    hoist_property_reversible h t (SObject m) s' prf | (Just (SObject hm), Nothing) with (get t hm) proof prf2
        hoist_property_reversible _ _ (SObject _) _ prf | (Just (SObject _), Nothing) | Nothing = absurd $ prf
        hoist_property_reversible h t (SObject m) s' prf | (Just (SObject hm), Nothing) | Just x =
            rewrite sym $ justInjective prf in
            let neq_ht = get_neq (tuple_eq prf1 uninhabited)
                neq_th = \p => neq_ht (sym p) in
            rewrite update_permute m h t (Just (SObject (update t Nothing hm))) (Just x) neq_ht in
            rewrite ne_key t h neq_th in
            rewrite beq_key t in
            rewrite beq_key h in
            rewrite beq_key t in
            rewrite update_permute m t h (Just x) (Just (SObject (update t Nothing hm))) neq_th in
            rewrite update_shadow hm t Nothing (Just x) in
            rewrite update_permute (update t (Just x) m) t h Nothing (Just (SObject (update t Nothing hm))) neq_th in
            rewrite update_shadow m t (Just x) Nothing in
            rewrite update_shadow (update t Nothing m) h
                (Just (SObject (update t Nothing hm)))
                (Just (SObject (update t (Just x) hm))) in
            rewrite update_same m t Nothing (cong snd prf1) in
            rewrite update_same hm t (Just x) prf2 in
            rewrite update_same m h (Just (SObject hm)) (cong fst prf1) in Refl

plunge_property_reversible : (h, t : Key) ->
    (s : Schema) -> (s' : Schema) ->
    transform_schema (PlungeProperty h t) s = Just s' -> transform_schema (reverse_lens (PlungeProperty h t)) s' = Just s
plunge_property_reversible _ _ SNull _ Refl impossible
plunge_property_reversible _ _ SBoolean _ Refl impossible
plunge_property_reversible _ _ SNumber _ Refl impossible
plunge_property_reversible _ _ SText _ Refl impossible
plunge_property_reversible _ _ (SArray _ _) _ Refl impossible
plunge_property_reversible h t (SObject m) s' prf with (get t m, get h m, t == h) proof prf1
    plunge_property_reversible _ _ (SObject _) _ prf | (Nothing, _, _) = absurd $ prf
    plunge_property_reversible _ _ (SObject _) _ prf | (Just _, Nothing, _) = absurd $ prf
    plunge_property_reversible _ _ (SObject _) _ prf | (Just _, Just SNull, _) = absurd $ prf
    plunge_property_reversible _ _ (SObject _) _ prf | (Just _, Just SBoolean, _) = absurd $ prf
    plunge_property_reversible _ _ (SObject _) _ prf | (Just _, Just SNumber, _) = absurd $ prf
    plunge_property_reversible _ _ (SObject _) _ prf | (Just _, Just SText, _) = absurd $ prf
    plunge_property_reversible _ _ (SObject _) _ prf | (Just _, Just (SArray _ _), _) = absurd $ prf
    plunge_property_reversible _ _ (SObject _) _ prf | (Just _, Just (SObject _), True) = absurd $ prf
    plunge_property_reversible h t (SObject m) s' prf | (Just tv, Just (SObject hm), False) with (get t hm) proof prf2
        plunge_property_reversible _ _ (SObject _) _ prf | (Just _, Just (SObject _), False) | Just _ = absurd $ prf
        plunge_property_reversible h t (SObject m) s' prf | (Just tv, Just (SObject hm), False) | Nothing =
            rewrite sym $ justInjective prf in
            let neq_th = bne_key t h $ cong snd $ cong snd $ prf1
                neq_ht = \p => neq_th $ sym p in
            rewrite update_eq (update t Nothing m) h (Just (SObject (update t (Just tv) hm))) in
            rewrite update_permute m h t (Just (SObject (update t (Just tv) hm))) Nothing neq_ht in
            rewrite ne_key t h neq_th in
            rewrite beq_key t in
            rewrite beq_key t in
            rewrite update_shadow hm t (Just tv) Nothing in
            rewrite update_shadow (update h (Just (SObject (update t (Just tv) hm))) m) t Nothing (Just tv) in
            rewrite update_permute m t h (Just tv) (Just (SObject (update t (Just tv) hm))) neq_th in
            rewrite update_same m t (Just tv) (cong fst prf1) in
            rewrite update_shadow m h (Just (SObject (update t (Just tv) hm))) (Just (SObject (update t Nothing hm))) in
            rewrite update_same hm t Nothing prf2 in
            rewrite update_same m h (Just (SObject hm)) (cong fst $ cong snd prf1) in Refl

wrap_reversible :
    (s : Schema) -> (s' : Schema) ->
    transform_schema Wrap s = Just s' -> transform_schema (reverse_lens Wrap) s' = Just s
wrap_reversible SNull _ prf = rewrite sym $ justInjective prf in Refl
wrap_reversible SBoolean _ prf = rewrite sym $ justInjective prf in Refl
wrap_reversible SNumber _ prf = rewrite sym $ justInjective prf in Refl
wrap_reversible SText _ prf = rewrite sym $ justInjective prf in Refl
wrap_reversible (SArray _ _) _ prf = rewrite sym $ justInjective prf in Refl
wrap_reversible (SObject _) _ prf = rewrite sym $ justInjective prf in Refl

head_reversible :
    (s : Schema) -> (s' : Schema) ->
    transform_schema Head s = Just s' -> transform_schema (reverse_lens Head) s' = Just s
head_reversible SNull _ Refl impossible
head_reversible SBoolean _ Refl impossible
head_reversible SNumber _ Refl impossible
head_reversible SText _ Refl impossible
head_reversible (SArray False _) _ prf = rewrite sym $ justInjective prf in Refl
head_reversible (SArray True _) _ Refl impossible
head_reversible (SObject _) _ Refl impossible

convert_reversible : (k, k' : PrimitiveKind) -> (m : List (PrimitiveValue, PrimitiveValue)) ->
    (s : Schema) -> (s' : Schema) ->
    transform_schema (Convert k k' m) s = Just s' -> transform_schema (reverse_lens (Convert k k' m)) s' = Just s
convert_reversible k k' m s s' prf with (validate_map k k' m) proof prf1
    convert_reversible KBoolean KBoolean _ _ _ prf | False = absurd $ prf
    convert_reversible KBoolean KNumber _ _ _ prf | False = absurd $ prf
    convert_reversible KBoolean KText _ _ _ prf | False = absurd $ prf
    convert_reversible KNumber KBoolean _ _ _ prf | False = absurd $ prf
    convert_reversible KNumber KNumber _ _ _ prf | False = absurd $ prf
    convert_reversible KNumber KText _ _ _ prf | False = absurd $ prf
    convert_reversible KText KBoolean _ _ _ prf | False = absurd $ prf
    convert_reversible KText KNumber _ _ _ prf | False = absurd $ prf
    convert_reversible KText KText _ _ _ prf | False = absurd $ prf
    convert_reversible KBoolean KBoolean _ SNull _ prf | True = absurd $ prf
    convert_reversible KBoolean KBoolean _ SBoolean SNull prf | True = absurd $ justInjective prf
    convert_reversible KBoolean KBoolean m SBoolean SBoolean prf | True =
        rewrite sym $ justInjective prf in
        rewrite flip_map_preserves_validity KBoolean KBoolean m prf1 in Refl
    convert_reversible KBoolean KBoolean _ SBoolean SNumber prf | True = absurd $ justInjective prf
    convert_reversible KBoolean KBoolean _ SBoolean SText prf | True = absurd $ justInjective prf
    convert_reversible KBoolean KBoolean _ SBoolean (SArray _ _) prf | True = absurd $ justInjective prf
    convert_reversible KBoolean KBoolean _ SBoolean (SObject _) prf | True = absurd $ justInjective prf
    convert_reversible KBoolean KBoolean _ SNumber _ prf | True = absurd $ prf
    convert_reversible KBoolean KBoolean _ SText _ prf | True = absurd $ prf
    convert_reversible KBoolean KBoolean _ (SArray _ _) _ prf | True = absurd $ prf
    convert_reversible KBoolean KBoolean _ (SObject _) _ prf | True = absurd $ prf
    convert_reversible KBoolean KNumber _ SNull _ prf | True = absurd $ prf
    convert_reversible KBoolean KNumber _ SBoolean SNull prf | True = absurd $ justInjective prf
    convert_reversible KBoolean KNumber _ SBoolean SBoolean prf | True = absurd $ justInjective prf
    convert_reversible KBoolean KNumber m SBoolean SNumber prf | True =
        rewrite sym $ justInjective prf in
        rewrite flip_map_preserves_validity KBoolean KNumber m prf1 in Refl
    convert_reversible KBoolean KNumber _ SBoolean SText prf | True = absurd $ justInjective prf
    convert_reversible KBoolean KNumber _ SBoolean (SArray _ _) prf | True = absurd $ justInjective prf
    convert_reversible KBoolean KNumber _ SBoolean (SObject _) prf | True = absurd $ justInjective prf
    convert_reversible KBoolean KNumber _ SNumber _ prf | True = absurd $ prf
    convert_reversible KBoolean KNumber _ SText _ prf | True = absurd $ prf
    convert_reversible KBoolean KNumber _ (SArray _ _) _ prf | True = absurd $ prf
    convert_reversible KBoolean KNumber _ (SObject _) _ prf | True = absurd $ prf
    convert_reversible KBoolean KText _ SNull _ prf | True = absurd $ prf
    convert_reversible KBoolean KText _ SBoolean SNull prf | True = absurd $ justInjective prf
    convert_reversible KBoolean KText _ SBoolean SBoolean prf | True = absurd $ justInjective prf
    convert_reversible KBoolean KText _ SBoolean SNumber prf | True = absurd $ justInjective prf
    convert_reversible KBoolean KText m SBoolean SText prf | True =
        rewrite sym $ justInjective prf in
        rewrite flip_map_preserves_validity KBoolean KText m prf1 in Refl
    convert_reversible KBoolean KText _ SBoolean (SArray _ _) prf | True = absurd $ justInjective prf
    convert_reversible KBoolean KText _ SBoolean (SObject _) prf | True = absurd $ justInjective prf
    convert_reversible KBoolean KText _ SNumber _ prf | True = absurd $ prf
    convert_reversible KBoolean KText _ SText _ prf | True = absurd $ prf
    convert_reversible KBoolean KText _ (SArray _ _) _ prf | True = absurd $ prf
    convert_reversible KBoolean KText _ (SObject _) _ prf | True = absurd $ prf
    convert_reversible KNumber KBoolean _ SNull _ prf | True = absurd $ prf
    convert_reversible KNumber KBoolean _ SBoolean _ prf | True = absurd $ prf
    convert_reversible KNumber KBoolean _ SNumber SNull prf | True = absurd $ justInjective prf
    convert_reversible KNumber KBoolean m SNumber SBoolean prf | True =
        rewrite sym $ justInjective prf in
        rewrite flip_map_preserves_validity KNumber KBoolean m prf1 in Refl
    convert_reversible KNumber KBoolean _ SNumber SNumber prf | True = absurd $ justInjective prf
    convert_reversible KNumber KBoolean _ SNumber SText prf | True = absurd $ justInjective prf
    convert_reversible KNumber KBoolean _ SNumber (SArray _ _) prf | True = absurd $ justInjective prf
    convert_reversible KNumber KBoolean _ SNumber (SObject _) prf | True = absurd $ justInjective prf
    convert_reversible KNumber KBoolean _ SText _ prf | True = absurd $ prf
    convert_reversible KNumber KBoolean _ (SArray _ _) _ prf | True = absurd $ prf
    convert_reversible KNumber KBoolean _ (SObject _) _ prf | True = absurd $ prf
    convert_reversible KNumber KNumber _ SNull _ prf | True = absurd $ prf
    convert_reversible KNumber KNumber _ SBoolean _ prf | True = absurd $ prf
    convert_reversible KNumber KNumber _ SNumber SNull prf | True = absurd $ justInjective prf
    convert_reversible KNumber KNumber _ SNumber SBoolean prf | True = absurd $ justInjective prf
    convert_reversible KNumber KNumber m SNumber SNumber prf | True =
        rewrite sym $ justInjective prf in
        rewrite flip_map_preserves_validity KNumber KNumber m prf1 in Refl
    convert_reversible KNumber KNumber _ SNumber SText prf | True = absurd $ justInjective prf
    convert_reversible KNumber KNumber _ SNumber (SArray _ _) prf | True = absurd $ justInjective prf
    convert_reversible KNumber KNumber _ SNumber (SObject _) prf | True = absurd $ justInjective prf
    convert_reversible KNumber KNumber _ SText _ prf | True = absurd $ prf
    convert_reversible KNumber KNumber _ (SArray _ _) _ prf | True = absurd $ prf
    convert_reversible KNumber KNumber _ (SObject _) _ prf | True = absurd $ prf
    convert_reversible KNumber KText _ SNull _ prf | True = absurd $ prf
    convert_reversible KNumber KText _ SBoolean _ prf | True = absurd $ prf
    convert_reversible KNumber KText _ SNumber SNull prf | True = absurd $ justInjective prf
    convert_reversible KNumber KText _ SNumber SBoolean prf | True = absurd $ justInjective prf
    convert_reversible KNumber KText _ SNumber SNumber prf | True = absurd $ justInjective prf
    convert_reversible KNumber KText m SNumber SText prf | True =
        rewrite sym $ justInjective prf in
        rewrite flip_map_preserves_validity KNumber KText m prf1 in Refl
    convert_reversible KNumber KText _ SNumber (SArray _ _) prf | True = absurd $ justInjective prf
    convert_reversible KNumber KText _ SNumber (SObject _) prf | True = absurd $ justInjective prf
    convert_reversible KNumber KText _ SText _ prf | True = absurd $ prf
    convert_reversible KNumber KText _ (SArray _ _) _ prf | True = absurd $ prf
    convert_reversible KNumber KText _ (SObject _) _ prf | True = absurd $ prf
    convert_reversible KText KBoolean _ SNull _ prf | True = absurd $ prf
    convert_reversible KText KBoolean _ SBoolean _ prf | True = absurd $ prf
    convert_reversible KText KBoolean _ SNumber _ prf | True = absurd $ prf
    convert_reversible KText KBoolean _ SText SNull prf | True = absurd $ justInjective prf
    convert_reversible KText KBoolean m SText SBoolean prf | True =
        rewrite sym $ justInjective prf in
        rewrite flip_map_preserves_validity KText KBoolean m prf1 in Refl
    convert_reversible KText KBoolean _ SText SNumber prf | True = absurd $ justInjective prf
    convert_reversible KText KBoolean _ SText SText prf | True = absurd $ justInjective prf
    convert_reversible KText KBoolean _ SText (SArray _ _) prf | True = absurd $ justInjective prf
    convert_reversible KText KBoolean _ SText (SObject _) prf | True = absurd $ justInjective prf
    convert_reversible KText KBoolean _ (SArray _ _) _ prf | True = absurd $ prf
    convert_reversible KText KBoolean _ (SObject _) _ prf | True = absurd $ prf
    convert_reversible KText KNumber _ SNull _ prf | True = absurd $ prf
    convert_reversible KText KNumber _ SBoolean _ prf | True = absurd $ prf
    convert_reversible KText KNumber _ SNumber _ prf | True = absurd $ prf
    convert_reversible KText KNumber _ SText SNull prf | True = absurd $ justInjective prf
    convert_reversible KText KNumber _ SText SBoolean prf | True = absurd $ justInjective prf
    convert_reversible KText KNumber m SText SNumber prf | True =
        rewrite sym $ justInjective prf in
        rewrite flip_map_preserves_validity KText KNumber m prf1 in Refl
    convert_reversible KText KNumber _ SText SText prf | True = absurd $ justInjective prf
    convert_reversible KText KNumber _ SText (SArray _ _) prf | True = absurd $ justInjective prf
    convert_reversible KText KNumber _ SText (SObject _) prf | True = absurd $ justInjective prf
    convert_reversible KText KNumber _ (SArray _ _) _ prf | True = absurd $ prf
    convert_reversible KText KNumber _ (SObject _) _ prf | True = absurd $ prf
    convert_reversible KText KText _ SNull _ prf | True = absurd $ prf
    convert_reversible KText KText _ SBoolean _ prf | True = absurd $ prf
    convert_reversible KText KText _ SNumber _ prf | True = absurd $ prf
    convert_reversible KText KText _ SText SNull prf | True = absurd $ justInjective prf
    convert_reversible KText KText _ SText SBoolean prf | True = absurd $ justInjective prf
    convert_reversible KText KText _ SText SNumber prf | True = absurd $ justInjective prf
    convert_reversible KText KText m SText SText prf | True =
        rewrite sym $ justInjective prf in
        rewrite flip_map_preserves_validity KText KText m prf1 in Refl
    convert_reversible KText KText _ SText (SArray _ _) prf | True = absurd $ justInjective prf
    convert_reversible KText KText _ SText (SObject _) prf | True = absurd $ justInjective prf
    convert_reversible KText KText _ (SArray _ _) _ prf | True = absurd $ prf
    convert_reversible KText KText _ (SObject _) _ prf | True = absurd $ prf


||| Forwards and backwards compatibility requires schema transformations to be reversible
lens_reversible : (l : Lens) -> (s : Schema) -> (s' : Schema) ->
    transform_schema l s = Just s' -> transform_schema (reverse_lens l) s' = Just s
lens_reversible (Make k) s s' prf = make_reversible k s s' prf
lens_reversible (Destroy k) s s' prf = destroy_reversible k s s' prf
lens_reversible (AddProperty k) s s' prf = add_property_reversible k s s' prf
lens_reversible (RemoveProperty k) s s' prf = remove_property_reversible k s s' prf
lens_reversible (RenameProperty k k') s s' prf = rename_property_reversible k k' s s' prf
lens_reversible (HoistProperty h t) s s' prf = hoist_property_reversible h t s s' prf
lens_reversible (PlungeProperty h t) s s' prf = plunge_property_reversible h t s s' prf
lens_reversible Wrap s s' prf = wrap_reversible s s' prf
lens_reversible Head s s' prf = head_reversible s s' prf
lens_reversible (LensIn _ _) SNull _ Refl impossible
lens_reversible (LensIn _ _) SBoolean _ Refl impossible
lens_reversible (LensIn _ _) SNumber _ Refl impossible
lens_reversible (LensIn _ _) SText _ Refl impossible
lens_reversible (LensIn _ _) (SArray _ _) _ Refl impossible
lens_reversible (LensIn k l) (SObject m) s' prf with (get k m) proof prf1
    lens_reversible (LensIn k l) (SObject m) s' prf | Nothing = absurd $ prf
    lens_reversible (LensIn k l) (SObject m) s' prf | (Just s2) with (transform_schema l s2) proof prf2
        lens_reversible (LensIn k l) (SObject m) s' prf | (Just s2) | Nothing = absurd $ prf
        lens_reversible (LensIn k l) (SObject m) s' prf | (Just s2) | (Just s2') =
            rewrite sym $ justInjective prf in
            rewrite update_eq m k (Just s2') in
            rewrite lens_reversible l s2 s2' prf2 in
            rewrite update_shadow m k (Just s2') (Just s2) in
            rewrite update_same m k (Just s2) prf1 in Refl
lens_reversible (LensMap _) SNull _ Refl impossible
lens_reversible (LensMap _) SBoolean _ Refl impossible
lens_reversible (LensMap _) SNumber _ Refl impossible
lens_reversible (LensMap _) SText _ Refl impossible
lens_reversible (LensMap l) (SArray e s2) s' prf with (transform_schema l s2) proof prf1
    lens_reversible (LensMap l) (SArray e s2) s' prf | Nothing = absurd $ prf
    lens_reversible (LensMap l) (SArray e s2) s' prf | (Just s2') =
        rewrite sym $ justInjective prf in
        rewrite lens_reversible l s2 s2' prf1 in Refl
lens_reversible (LensMap _) (SObject _) _ Refl impossible
lens_reversible (Convert k k' m) s s' prf = convert_reversible k k' m s s' prf
