// Auto-generated by GenerateSteppedRangesCodegenTestData. Do not edit!
// KJS_WITH_FULL_RUNTIME
// WITH_RUNTIME
import kotlin.test.*

fun box(): String {
    val uintList = mutableListOf<UInt>()
    val uintProgression = 1u until 9u
    for (i in uintProgression step 2 step 3) {
        uintList += i
    }
    assertEquals(listOf(1u, 4u, 7u), uintList)

    val ulongList = mutableListOf<ULong>()
    val ulongProgression = 1uL until 9uL
    for (i in ulongProgression step 2L step 3L) {
        ulongList += i
    }
    assertEquals(listOf(1uL, 4uL, 7uL), ulongList)

    return "OK"
}