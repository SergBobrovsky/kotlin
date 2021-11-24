import org.jetbrains.kotlin.ideaExt.idea

plugins {
    kotlin("jvm")
    id("jps-compatible")
}

dependencies {
    testApi(project(":plugins:fir-plugin-prototype"))
    testApi(project(":compiler:incremental-compilation-impl"))
    testApi(projectTests(":compiler:incremental-compilation-impl"))

    testCompileOnly(intellijCore())
    testCompileOnly(project(":kotlin-reflect-api"))

    testRuntimeOnly(project(":kotlin-reflect"))
    testRuntimeOnly(project(":core:descriptors.runtime"))
    testRuntimeOnly(project(":compiler:fir:fir-serialization"))

    testRuntimeOnly(intellijDependency("lz4-java"))
    testRuntimeOnly(intellijDependency("jna"))
    testRuntimeOnly(intellijDependency("jdom"))
    testRuntimeOnly(intellijDependency("trove4j"))
    testRuntimeOnly(intellijDependency("intellij-deps-fastutil"))

    testRuntimeOnly(toolsJar())
}

val generationRoot = projectDir.resolve("tests-gen")

sourceSets {
    "main" {
        projectDefault()
    }
    "test" {
        projectDefault()
        this.java.srcDir(generationRoot.name)
    }
}

if (kotlinBuildProperties.isInJpsBuildIdeaSync) {
    apply(plugin = "idea")
    idea {
        this.module.generatedSourceDirs.add(generationRoot)
    }
}

projectTest(parallel = true, jUnitMode = JUnitMode.JUnit4) {
    workingDir = rootDir
    useJUnitPlatform()
    jvmArgs!!.removeIf { it.contains("-Xmx") }
    maxHeapSize = "3g"
    dependsOn(":plugins:fir-plugin-prototype:jar")
    dependsOn(":plugins:fir-plugin-prototype:plugin-annotations:jar")
}

testsJar()
