module Lens.Uninhabited

import Lens
import Map

%default total

public export
Uninhabited (a = b) => Uninhabited (Boolean a = Boolean b) where
    uninhabited Refl @{ab} = uninhabited @{ab} Refl

public export
Uninhabited (Boolean a = Number b) where
    uninhabited Refl impossible

public export
Uninhabited (Boolean a = Text b) where
    uninhabited Refl impossible

public export
Uninhabited (a = b) => Uninhabited (Number a = Number b) where
    uninhabited Refl @{ab} = uninhabited @{ab} Refl

public export
Uninhabited (Number a = Boolean b) where
    uninhabited Refl impossible

public export
Uninhabited (Number a = Text b) where
    uninhabited Refl impossible

public export
Uninhabited (a = b) => Uninhabited (Text a = Text b) where
    uninhabited Refl @{ab} = uninhabited @{ab} Refl

public export
Uninhabited (Text a = Boolean b) where
    uninhabited Refl impossible

public export
Uninhabited (Text a = Number b) where
    uninhabited Refl impossible


public export
Uninhabited (KBoolean = KNumber) where
    uninhabited Refl impossible

public export
Uninhabited (KBoolean = KText) where
    uninhabited Refl impossible

public export
Uninhabited (KNumber = KBoolean) where
    uninhabited Refl impossible

public export
Uninhabited (KNumber = KText) where
    uninhabited Refl impossible

public export
Uninhabited (KText = KBoolean) where
    uninhabited Refl impossible

public export
Uninhabited (KText = KNumber) where
    uninhabited Refl impossible


public export
Uninhabited (Null = Primitive _) where
    uninhabited Refl impossible

public export
Uninhabited (Null = Array _) where
    uninhabited Refl impossible

public export
Uninhabited (Null = Object _) where
    uninhabited Refl impossible

public export
Uninhabited (Primitive _ = Null) where
    uninhabited Refl impossible

public export
Uninhabited (a = b) => Uninhabited (Primitive a = Primitive b) where
    uninhabited Refl @{ab} = uninhabited @{ab} Refl

public export
Uninhabited (Primitive _ = Array _) where
    uninhabited Refl impossible

public export
Uninhabited (Primitive _ = Object _) where
    uninhabited Refl impossible

public export
Uninhabited (Array _ = Null) where
    uninhabited Refl impossible

public export
Uninhabited (Array _ = Primitive _) where
    uninhabited Refl impossible

public export
Uninhabited (a = b) => Uninhabited (Array a = Array b) where
    uninhabited Refl @{ab} = uninhabited @{ab} Refl

public export
Uninhabited (Array _ = Object _) where
    uninhabited Refl impossible

public export
Uninhabited (Object _ = Null) where
    uninhabited Refl impossible

public export
Uninhabited (Object _ = Primitive _) where
    uninhabited Refl impossible

public export
Uninhabited (Object _ = Array _) where
    uninhabited Refl impossible

public export
Uninhabited (a = b) => Uninhabited (Object a = Object b) where
    uninhabited Refl @{ab} = uninhabited @{ab} Refl


public export
Uninhabited (SNull = SBoolean) where
    uninhabited Refl impossible

public export
Uninhabited (SNull = SNumber) where
    uninhabited Refl impossible

public export
Uninhabited (SNull = SText) where
    uninhabited Refl impossible

public export
Uninhabited (SNull = SArray _ _) where
    uninhabited Refl impossible

public export
Uninhabited (SNull = SObject _) where
    uninhabited Refl impossible

public export
Uninhabited (SBoolean = SNull) where
    uninhabited Refl impossible

public export
Uninhabited (SBoolean = SNumber) where
    uninhabited Refl impossible

public export
Uninhabited (SBoolean = SText) where
    uninhabited Refl impossible

public export
Uninhabited (SBoolean = SArray _ _) where
    uninhabited Refl impossible

public export
Uninhabited (SBoolean = SObject _) where
    uninhabited Refl impossible

public export
Uninhabited (SNumber = SNull) where
    uninhabited Refl impossible

public export
Uninhabited (SNumber = SBoolean) where
    uninhabited Refl impossible

public export
Uninhabited (SNumber = SText) where
    uninhabited Refl impossible

public export
Uninhabited (SNumber = SArray _ _) where
    uninhabited Refl impossible

public export
Uninhabited (SNumber = SObject _) where
    uninhabited Refl impossible

public export
Uninhabited (SText = SNull) where
    uninhabited Refl impossible

public export
Uninhabited (SText = SBoolean) where
    uninhabited Refl impossible

public export
Uninhabited (SText = SNumber) where
    uninhabited Refl impossible

public export
Uninhabited (SText = SArray _ _) where
    uninhabited Refl impossible

public export
Uninhabited (SText = SObject _) where
    uninhabited Refl impossible

public export
Uninhabited (SArray _ _ = SNull) where
    uninhabited Refl impossible

public export
Uninhabited (SArray _ _ = SBoolean) where
    uninhabited Refl impossible

public export
Uninhabited (SArray _ _ = SNumber) where
    uninhabited Refl impossible

public export
Uninhabited (SArray _ _ = SText) where
    uninhabited Refl impossible

public export
Uninhabited (a = b) => Uninhabited (SArray a _ = SArray b _) where
    uninhabited Refl @{ab} = uninhabited @{ab} Refl

public export
Uninhabited (a = b) => Uninhabited (SArray _ a = SArray _ b) where
    uninhabited Refl @{ab} = uninhabited @{ab} Refl

public export
Uninhabited (SArray _ _ = SObject _) where
    uninhabited Refl impossible

public export
Uninhabited (SObject _ = SNull) where
    uninhabited Refl impossible

public export
Uninhabited (SObject _ = SBoolean) where
    uninhabited Refl impossible

public export
Uninhabited (SObject _ = SNumber) where
    uninhabited Refl impossible

public export
Uninhabited (SObject _ = SText) where
    uninhabited Refl impossible

public export
Uninhabited (SObject _ = SArray _ _) where
    uninhabited Refl impossible

public export
Uninhabited (a = b) => Uninhabited (SObject a = SObject b) where
    uninhabited Refl @{ab} = uninhabited @{ab} Refl
