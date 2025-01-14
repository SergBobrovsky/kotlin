/*
 * Copyright 2010-2021 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */
package kotlin.time

internal actual inline val durationAssertionsEnabled: Boolean get() = true
internal actual fun formatToExactDecimals(value: Double, decimals: Int): String = TODO("Wasm stdlib: Duration")
internal actual fun formatUpToDecimals(value: Double, decimals: Int): String = TODO("Wasm stdlib: Duration")