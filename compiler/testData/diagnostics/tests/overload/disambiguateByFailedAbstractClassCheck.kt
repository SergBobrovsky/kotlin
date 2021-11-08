// FIR_IDENTICAL
// !WITH_NEW_IFERENCE
// !LANGUAGE: +NewInference
// !DIAGNOSTICS: -UNUSED_PARAMETER

// FILE: packageA.kt

package a

abstract class Cls
abstract class Cls2

// FILE: packageB.kt

package b

fun Cls() {}
class Cls2

// FILE: test.kt

package c

import a.*
import b.*

fun take(arg: Any) {}

fun test() {
    <!OVERLOAD_RESOLUTION_AMBIGUITY!>Cls<!>()
    take(<!OVERLOAD_RESOLUTION_AMBIGUITY!>Cls<!>())

    <!INAPPLICABLE_CANDIDATE!>Cls2<!>()
    take(<!INAPPLICABLE_CANDIDATE!>Cls2<!>())
}
