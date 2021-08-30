module Map

import Data.List
import Data.Maybe
import Data.Nat

%default total

iff : (p, q : Type) -> Type
iff p q = (p -> q, q -> p)

iff_sym : iff p q -> iff q p
iff_sym (x, y) = (y, x)

functional_extensionality : ((x : a) -> f x = g x) -> f = g
functional_extensionality = believe_me

public export
data Reflect : (p: Type) -> (b: Bool) -> Type where
    ReflectT : p -> (b=True) -> Reflect p b
    ReflectF : (Not p) -> (b=False) -> Reflect p b

iff_reflect : (b : Bool) -> iff p (b = True) -> Reflect p b
iff_reflect False (x, y) = ReflectF (uninhabited . x) Refl
iff_reflect True (x, y) = ReflectT (y Refl) Refl

reflect_iff : (b : Bool) -> Reflect p b -> iff p (b = True)
reflect_iff False (ReflectT _ Refl) impossible
reflect_iff False (ReflectF f prf) = (\p => void (f p), \p => void (uninhabited p))
reflect_iff True (ReflectT x prf) = (\p => prf, \Refl => x)
reflect_iff True (ReflectF _ Refl) impossible

public export
beq_bool : (b : Bool) -> b == b = True
beq_bool False = Refl
beq_bool True = Refl

public export
eq_bool : (b1, b2 : Bool) -> b1 == b2 = True -> b1 = b2
eq_bool False False _ = Refl
eq_bool False True Refl impossible
eq_bool True False Refl impossible
eq_bool True True _ = Refl

public export
neq_bool : (b1, b2 : Bool) -> b1 == b2 = False -> Not (b1 = b2)
neq_bool False False prf = absurd $ prf
neq_bool False True prf = uninhabited
neq_bool True False prf = uninhabited
neq_bool True True prf = absurd $ prf

public export
inv_bool : (b1, b2 : Bool) -> b1 = (not b2) -> b2 = (not b1)
inv_bool False False Refl impossible
inv_bool False True _ = Refl
inv_bool True False _ = Refl
inv_bool True True Refl impossible

public export
and_split : (a : Bool) -> (b : Lazy Bool) -> a && b = True -> (a = True, b = True)
and_split False (Delay b) prf = absurd prf
and_split True (Delay b) prf = (Refl, prf)

public export
and_join : (a = True, b = True) -> a && b = True
and_join (x, y) = rewrite x in rewrite y in Refl

public export
and_join2 : a = False -> a && _ = False
and_join2 prf = rewrite prf in Refl

public export
tuple_eq : (a, b) = (c, d) -> Not (c = d) -> Not (a = b)
tuple_eq prf f prf1 =
    let
        ac = cong fst prf
        bd = cong snd prf
    in f (rewrite sym ac in rewrite sym bd in prf1)


-- Maybe utils
public export
it_is_just : (a : Maybe b) -> (a = Just c) -> IsJust a
it_is_just Nothing Refl impossible
it_is_just (Just x) prf = ItIsJust


public export
contra : IsJust a -> a = Nothing -> Void
contra ItIsJust Refl impossible


-- Nat utils
public export
beq_nat : (n : Nat) -> n == n = True
beq_nat 0 = Refl
beq_nat (S k) = beq_nat k

public export
eq_nat : (n1, n2 : Nat) -> n1 == n2 = True -> n1 = n2
eq_nat 0 0 prf = Refl
eq_nat 0 (S _) Refl impossible
eq_nat (S _) 0 Refl impossible
eq_nat (S k) (S j) prf =
    let ind = eq_nat k j prf in
        rewrite ind in Refl

public export
neq_nat : (n1, n2 : Nat) -> n1 == n2 = False -> Not (n1 = n2)
neq_nat 0 0 prf = absurd prf
neq_nat 0 (S k) Refl = uninhabited
neq_nat (S k) 0 Refl = uninhabited
neq_nat (S k) (S j) prf =
    let ind = neq_nat k j prf in
        \p => ind $ cong pred p

beq_natP : (n, m : Nat) -> Reflect (n = m) (n == m)
beq_natP n m with (n == m) proof h
    beq_natP n m | False = ReflectF (neq_nat n m h) Refl
    beq_natP n m | True = ReflectT (eq_nat n m h) Refl


-- String utils
public export
beq_str : (s : List Char) -> s == s = True
beq_str s = believe_me s

public export
eq_str : (s1, s2 : List Char) -> s1 == s2 = True -> s1 = s2
eq_str s1 s2 prf = believe_me prf

public export
neq_str : (s1, s2 : List Char) -> s1 == s2 = False -> Not (s1 = s2)
neq_str s1 s2 prf = believe_me prf


-- Key
public export
data Key : Type where
    MkKey : Nat -> Key

%name Key k, k1, k2

key_to_nat : Key -> Nat
key_to_nat (MkKey n) = n

public export
Eq Key where
    MkKey a == MkKey b = a == b

public export
Uninhabited (a = b) => Uninhabited (MkKey a = MkKey b) where
    uninhabited Refl @{ab} = uninhabited @{ab} Refl

public export
beq_key : (k: Key) -> k == k = True
beq_key (MkKey n) = beq_nat n

public export
bne_key : (k1, k2 : Key) -> k1 == k2 = False -> Not (k1 = k2)
bne_key (MkKey k) (MkKey j) prf prf1 =
    neq_nat k j prf (cong key_to_nat prf1)

public export
ne_key : (k1, k2 : Key) -> Not (k1 = k2) -> k1 == k2 = False
ne_key (MkKey k) (MkKey j) with (beq_natP k j)
    ne_key (MkKey k) (MkKey j) | (ReflectT x prf) = \a => void $ a $ cong MkKey x
    ne_key (MkKey k) (MkKey j) | (ReflectF f prf) = \a => prf

public export
beq_keyP : (n, m : Key) -> Reflect (n = m) (n == m)
beq_keyP (MkKey k) (MkKey j) with (beq_natP k j)
    beq_keyP (MkKey k) (MkKey j) | (ReflectT x prf) = ReflectT (cong MkKey x) prf
    beq_keyP (MkKey k) (MkKey j) | (ReflectF f prf) = ReflectF (\p => f (cong key_to_nat p)) prf

public export
data Map : Type -> Type where
    Empty : Map a
    Update : Key -> Maybe a -> Map a -> Map a

%name Map m, m1, m2

public export
Uninhabited (Empty = Update k v m) where
    uninhabited Refl impossible

public export
Uninhabited (Update k v m = Empty) where
    uninhabited Refl impossible

public export
empty : Map a
empty = Empty

public export
update : Key -> Maybe a -> Map a -> Map a
update k v m = Update k v m

public export
insert : Key -> a -> Map a -> Map a
insert k v m = update k (Just v) m

public export
remove : Key -> Map a -> Map a
remove k m = update k Nothing m

public export
get : Key -> Map a -> Maybe a
get k Empty = Nothing
get k (Update k' v' m') = if k == k' then v' else get k m'

public export
contains : Key -> Map a -> Bool
contains k m = isJust $ get k m

public export
half_eq : Eq a => Map a -> Map a -> Bool
half_eq Empty _ = True
half_eq (Update k v m') m2 = get k m2 == v

public export
Eq a => Eq (Map a) where
    x == y = half_eq x y && half_eq y x

public export
keys : Map a -> List Key
keys m = filter (\k => contains k m) (all_keys m) where
    all_keys : Map a  -> List Key
    all_keys Empty = []
    all_keys (Update k _ m) = k :: all_keys m

public export
contains_all : List Key -> Map a -> Bool
contains_all [] m = True
contains_all (x :: xs) m = contains x m && contains_all xs m

public export
half_keys_eq : Map a -> Map b -> Bool
half_keys_eq m1 m2 = contains_all (keys m1) m2

public export
keys_eq : Map a -> Map b -> Bool
keys_eq m1 m2 = half_keys_eq m1 m2 && half_keys_eq m2 m1


-- Contains theorems
public export
get_just_contains : get k m = Just _ -> contains k m = True
get_just_contains prf = rewrite prf in Refl

public export
get_nothing_contains : get k m = Nothing -> contains k m = False
get_nothing_contains prf = rewrite prf in Refl


-- Get theorems
public export
get_neq : Not (get a m = get b m) -> Not (a = b)
get_neq f prf = f (cong (\k => get k m) prf)


-- Update theorems
public export
map_extensionality : (m1, m2 : Map a) -> ((k : Key) -> get k m1 = get k m2) -> m1 = m2
map_extensionality = \m1, m2, f => believe_me (Refl {x = MkUnit})

public export
update_eq : (m : Map a) -> (k : Key) -> (v : Maybe a) -> get k (update k v m) = v
update_eq m k v = rewrite beq_key k in Refl

public export
update_neq : (m : Map a) -> (k1, k2 : Key) -> (v : Maybe a) -> Not (k1 = k2) -> (get k2 $ update k1 v m) = get k2 m
update_neq m k1 k2 v f with (beq_keyP k2 k1)
    update_neq m k1 k2 v f | (ReflectT x prf) = void $ f $ sym x
    update_neq m k1 k2 v f | (ReflectF g prf) = rewrite prf in Refl

public export
update_shadow : (m : Map a) -> (k : Key) -> (v1, v2 : Maybe a) -> (update k v2 $ update k v1 m) = update k v2 m
update_shadow m k v1 v2 = map_extensionality (update k v2 $ update k v1 m) (update k v2 m) $ \k' =>
    case beq_keyP k' k of
        ReflectT t prf => rewrite prf in Refl
        ReflectF f prf => rewrite prf in rewrite prf in Refl

public export
update_same : (m : Map a) -> (k : Key) -> (v : Maybe a) -> (get k m = v) -> update k v m = m
update_same m k v prf = map_extensionality (update k v m) m  $ \k' =>
    case beq_keyP k' k of
        ReflectT t prf1 => rewrite prf1 in rewrite t in rewrite prf in Refl
        ReflectF f prf1 => rewrite prf1 in Refl

public export
update_permute : (m : Map a) -> (k1, k2 : Key) -> (v1, v2 : Maybe a) -> Not (k1 = k2) ->
    (update k1 v1 $ update k2 v2 m) = (update k2 v2 $ update k1 v1 m)
update_permute m k1 k2 v1 v2 prf = map_extensionality
    (update k1 v1 $ update k2 v2 m) (update k2 v2 $ update k1 v1 m) $ \k' =>
    case (beq_keyP k' k1, beq_keyP k' k2) of
        (ReflectT x _, ReflectT y _) =>
                void $ prf $ rewrite sym x in rewrite sym y in Refl
        (ReflectT _ prf1, ReflectF _ prf2) =>
            rewrite prf1 in rewrite prf2 in rewrite prf1 in Refl
        (ReflectF _ prf1, ReflectT _ prf2) =>
            rewrite prf1 in rewrite prf2 in Refl
        (ReflectF _ prf1, ReflectF _ prf2) =>
            rewrite prf1 in rewrite prf2 in rewrite prf1 in Refl


-- Half keys equality theorems
InMap : (k : Key) -> (m : Map a) -> Type
InMap k Empty = Void
InMap k (Update k' v' m') = Either (k = k', IsJust v') (Not (k = k'), InMap k m')

containsP : (k : Key) -> (m : Map a) -> Reflect (InMap k m) (contains k m)
containsP k Empty = ReflectF id Refl
containsP k (Update k' v' m') with (beq_keyP k k')
    containsP k (Update k' Nothing m') | ReflectT keq prf =
        rewrite prf in ReflectF (\f => case f of
            Left (_, f) => absurd f
            Right (f, _) => f keq) Refl
    containsP k (Update k' (Just v) m') | ReflectT keq prf =
        rewrite prf in ReflectT (Left (keq, ItIsJust)) Refl
    containsP k (Update k' v' m') | ReflectF f prf with (containsP k m')
        containsP k (Update k' v' m') | ReflectF f prf | ReflectT t prf1 =
            rewrite prf in ReflectT (Right (f, t)) prf1
        containsP k (Update k' v' m') | ReflectF f prf | ReflectF f' prf1 =
            rewrite prf in ReflectF (\p => case p of
                Left (p, _) => f p
                Right (_, p) => f' p) prf1

insert_contains : (k : Key) -> (v : a) -> (m : Map a) -> contains k (insert k v m) = True
insert_contains k v m = rewrite beq_key k in Refl

remove_contains : (k : Key) -> (m : Map a) -> contains k (remove k m) = False
remove_contains k m = rewrite beq_key k in Refl

contains_all_insert : (ks : List Key) -> (m : Map a) -> (k : Key) -> (v : a) ->
    contains_all ks m = True -> contains_all ks (insert k v m) = True
contains_all_insert [] _ _ _ _ = Refl
contains_all_insert (k :: ks) m k' v prf with (k == k')
    contains_all_insert (k :: ks) m k' v prf | False =
        let split = and_split (contains k m) (contains_all ks m) prf
            ind = contains_all_insert ks m k' v (snd split)
        in rewrite ind in rewrite fst split in Refl
    contains_all_insert (k :: ks) m k' v prf | True =
        let split = and_split (contains k m) (contains_all ks m) prf
            ind = contains_all_insert ks m k' v (snd split)
        in rewrite ind in Refl

contains_all_key : (ks : List Key) -> (m : Map a) -> (k : Key) -> contains k m = True ->
    contains_all ks m = True -> contains_all (k :: ks) m = True
contains_all_key ks m k prf prf1 = rewrite prf in rewrite prf1 in Refl

contains_all_key_insert : (ks : List Key) -> (m : Map a) -> (k : Key) -> (v : a) ->
    contains_all ks m = True -> contains_all (k :: ks) (insert k v m) = True
contains_all_key_insert ks m k v prf =
    let p = contains_all_insert ks m k v prf
        p' = contains_all_key ks (insert k v m) k (insert_contains k v m) p
    in p'

-- actually not true
keys_insert : (ks : List Key) -> (m : Map a) -> (k : Key) -> (v : a) ->
    keys m = ks -> keys (insert k v m) = k :: ks

public export
half_keys_eq_insert : (am : Map a) -> (bm : Map b) ->
    (k : Key) -> (av : a) -> (bv : b) ->
    half_keys_eq am bm = True -> half_keys_eq (insert k av am) (insert k bv bm) = True
half_keys_eq_insert am bm k av bv prf =
    let ki = keys_insert (keys am) am k av Refl
        p = contains_all_key_insert (keys am) bm k bv prf
    in rewrite ki in p

{-half_keys_eq_remove_right : (am : Map a) -> (bm : Map b) -> (k : Key) ->
    NotInMap k am -> half_keys_eq am bm = True -> half_keys_eq am (remove k bm) = True

half_keys_eq_remove_left : (am : Map a) -> (bm : Map b) -> (k : Key) ->
    half_keys_eq am bm = True -> half_keys_eq (remove k am) bm = True-}

public export
half_keys_eq_remove : (am : Map a) -> (bm : Map b) -> (k : Key) ->
    half_keys_eq am bm = True -> half_keys_eq (remove k am) (remove k bm) = True
{-half_keys_eq_remove am bm k prf =
    let left = half_keys_eq_remove_left am bm k prf
        right = half_keys_eq_remove_right (remove k am) bm k (remove_contains k am) left
    in right-}


public export
not_half_keys_eq : (am : Map a) -> (bm : Map b) -> (k : Key) ->
    contains k am = True -> contains k bm = False -> half_keys_eq am bm = False
