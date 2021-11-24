/*
 * Copyright 2010-2021 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.gradle.plugin.mpp.pm20.configuration

import org.gradle.api.NamedDomainObjectProvider
import org.gradle.api.artifacts.Configuration
import org.gradle.api.attributes.Bundling
import org.gradle.api.attributes.Category
import org.jetbrains.kotlin.gradle.plugin.mpp.pm20.*
import org.jetbrains.kotlin.gradle.plugin.mpp.pm20.KotlinFragmentModuleCapabilityConfigurator.setModuleCapability
import org.jetbrains.kotlin.gradle.plugin.mpp.pm20.util.FragmentNameDisambiguation
import org.jetbrains.kotlin.gradle.plugin.mpp.pm20.util.locateOrRegister

interface KotlinRuntimeElementsConfigurationFactory : KotlinFragmentConfigurationInstantiator

object DefaultKotlinRuntimeElementsConfigurationInstantiator : KotlinRuntimeElementsConfigurationFactory {
    override fun locateOrRegister(
        module: KotlinGradleModule,
        names: FragmentNameDisambiguation,
        dependencies: KotlinDependencyConfigurations
    ): NamedDomainObjectProvider<Configuration> {
        return module.project.configurations.locateOrRegister(names.disambiguateName("runtimeElements")) {
            isCanBeResolved = false
            isCanBeConsumed = false

            attributes.attribute(Category.CATEGORY_ATTRIBUTE, module.project.objects.named(Category::class.java, Category.LIBRARY))
            attributes.attribute(Bundling.BUNDLING_ATTRIBUTE, module.project.objects.named(Bundling::class.java, Bundling.EXTERNAL))

            extendsFrom(dependencies.transitiveApiConfiguration.get())
            extendsFrom(dependencies.transitiveImplementationConfiguration.get())
            module.ifMadePublic {
                isCanBeConsumed = true
                setModuleCapability(this, module)
            }
        }
    }
}

val DefaultKotlinRuntimeElementsConfigurator = KotlinConfigurationsConfigurator(
    KotlinFragmentPlatformAttributesConfigurator,
    KotlinFragmentProducerRuntimeUsageAttributesConfigurator
)
