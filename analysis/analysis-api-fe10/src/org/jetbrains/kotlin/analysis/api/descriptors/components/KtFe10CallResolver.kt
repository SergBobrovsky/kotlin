/*
 * Copyright 2010-2021 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.analysis.api.descriptors.components

import org.jetbrains.kotlin.analysis.api.calls.*
import org.jetbrains.kotlin.analysis.api.descriptors.Fe10AnalysisFacade.AnalysisMode
import org.jetbrains.kotlin.analysis.api.descriptors.KtFe10AnalysisSession
import org.jetbrains.kotlin.analysis.api.descriptors.components.base.Fe10KtAnalysisSessionComponent
import org.jetbrains.kotlin.analysis.api.descriptors.symbols.descriptorBased.KtFe10DescValueParameterSymbol
import org.jetbrains.kotlin.analysis.api.descriptors.symbols.descriptorBased.KtFe10ReceiverParameterSymbol
import org.jetbrains.kotlin.analysis.api.descriptors.symbols.descriptorBased.base.toKtCallableSymbol
import org.jetbrains.kotlin.analysis.api.descriptors.symbols.descriptorBased.base.toKtSymbol
import org.jetbrains.kotlin.analysis.api.descriptors.symbols.descriptorBased.base.toKtType
import org.jetbrains.kotlin.analysis.api.diagnostics.KtNonBoundToPsiErrorDiagnostic
import org.jetbrains.kotlin.analysis.api.impl.barebone.parentOfType
import org.jetbrains.kotlin.analysis.api.impl.base.components.AbstractKtCallResolver
import org.jetbrains.kotlin.analysis.api.symbols.*
import org.jetbrains.kotlin.analysis.api.tokens.ValidityToken
import org.jetbrains.kotlin.builtins.KotlinBuiltIns
import org.jetbrains.kotlin.descriptors.CallableDescriptor
import org.jetbrains.kotlin.descriptors.CallableMemberDescriptor
import org.jetbrains.kotlin.descriptors.PropertyDescriptor
import org.jetbrains.kotlin.descriptors.ValueParameterDescriptor
import org.jetbrains.kotlin.diagnostics.DiagnosticWithParameters1
import org.jetbrains.kotlin.diagnostics.DiagnosticWithParameters2
import org.jetbrains.kotlin.diagnostics.Errors
import org.jetbrains.kotlin.diagnostics.Severity
import org.jetbrains.kotlin.lexer.KtTokens
import org.jetbrains.kotlin.psi.*
import org.jetbrains.kotlin.psi.psiUtil.parentsWithSelf
import org.jetbrains.kotlin.resolve.BindingContext
import org.jetbrains.kotlin.resolve.calls.components.isVararg
import org.jetbrains.kotlin.resolve.calls.model.ResolvedCall
import org.jetbrains.kotlin.resolve.calls.model.VariableAsFunctionResolvedCall
import org.jetbrains.kotlin.resolve.calls.util.getResolvedCall
import org.jetbrains.kotlin.resolve.scopes.receivers.ExpressionReceiver
import org.jetbrains.kotlin.resolve.scopes.receivers.ExtensionReceiver
import org.jetbrains.kotlin.resolve.scopes.receivers.ImplicitReceiver
import org.jetbrains.kotlin.resolve.scopes.receivers.ReceiverValue
import org.jetbrains.kotlin.types.KotlinType
import org.jetbrains.kotlin.types.expressions.ControlStructureTypingUtils
import org.jetbrains.kotlin.util.OperatorNameConventions

internal class KtFe10CallResolver(
    override val analysisSession: KtFe10AnalysisSession
) : AbstractKtCallResolver(), Fe10KtAnalysisSessionComponent {
    private companion object {
        private val operatorWithAssignmentVariant = setOf(
            OperatorNameConventions.PLUS,
            OperatorNameConventions.MINUS,
            OperatorNameConventions.TIMES,
            OperatorNameConventions.DIV,
            OperatorNameConventions.REM,
            OperatorNameConventions.MOD,
        )

        private val callArgErrors = setOf(
            Errors.ARGUMENT_PASSED_TWICE,
            Errors.MIXING_NAMED_AND_POSITIONED_ARGUMENTS,
            Errors.NAMED_PARAMETER_NOT_FOUND,
            Errors.NAMED_ARGUMENTS_NOT_ALLOWED,
            Errors.VARARG_OUTSIDE_PARENTHESES,
            Errors.SPREAD_OF_NULLABLE,
            Errors.SPREAD_OF_LAMBDA_OR_CALLABLE_REFERENCE,
            Errors.MANY_LAMBDA_EXPRESSION_ARGUMENTS,
            Errors.UNEXPECTED_TRAILING_LAMBDA_ON_A_NEW_LINE,
            Errors.TOO_MANY_ARGUMENTS,
            Errors.REDUNDANT_SPREAD_OPERATOR_IN_NAMED_FORM_IN_FUNCTION,
            Errors.REDUNDANT_SPREAD_OPERATOR_IN_NAMED_FORM_IN_ANNOTATION,
            Errors.TYPE_MISMATCH,
        )
        private val resolutionFailureErrors = setOf(
            Errors.INVISIBLE_MEMBER,
            Errors.NO_VALUE_FOR_PARAMETER,
            Errors.MISSING_RECEIVER,
            Errors.NO_RECEIVER_ALLOWED,
            Errors.ILLEGAL_SELECTOR,
            Errors.FUNCTION_EXPECTED,
            Errors.FUNCTION_CALL_EXPECTED,
            Errors.NO_CONSTRUCTOR,
            Errors.OVERLOAD_RESOLUTION_AMBIGUITY,
            Errors.NONE_APPLICABLE,
            Errors.CANNOT_COMPLETE_RESOLVE,
            Errors.UNRESOLVED_REFERENCE_WRONG_RECEIVER,
            Errors.CALLABLE_REFERENCE_RESOLUTION_AMBIGUITY,
            Errors.TYPE_PARAMETER_AS_REIFIED,
            Errors.DEFINITELY_NON_NULLABLE_AS_REIFIED,
            Errors.REIFIED_TYPE_FORBIDDEN_SUBSTITUTION,
            Errors.REIFIED_TYPE_UNSAFE_SUBSTITUTION,
            Errors.CANDIDATE_CHOSEN_USING_OVERLOAD_RESOLUTION_BY_LAMBDA_ANNOTATION,
            Errors.RESOLUTION_TO_CLASSIFIER,
            Errors.RESERVED_SYNTAX_IN_CALLABLE_REFERENCE_LHS,
            Errors.PARENTHESIZED_COMPANION_LHS_DEPRECATION,
            Errors.RESOLUTION_TO_PRIVATE_CONSTRUCTOR_OF_SEALED_CLASS,
            Errors.UNRESOLVED_REFERENCE,
        )

        val diagnosticWithResolvedCallsAtPosition1 = setOf(
            Errors.OVERLOAD_RESOLUTION_AMBIGUITY,
            Errors.NONE_APPLICABLE,
            Errors.CANNOT_COMPLETE_RESOLVE,
            Errors.UNRESOLVED_REFERENCE_WRONG_RECEIVER,
            Errors.ASSIGN_OPERATOR_AMBIGUITY,
            Errors.ITERATOR_AMBIGUITY,
        )

        val diagnosticWithResolvedCallsAtPosition2 = setOf(
            Errors.COMPONENT_FUNCTION_AMBIGUITY,
            Errors.DELEGATE_SPECIAL_FUNCTION_AMBIGUITY,
            Errors.DELEGATE_SPECIAL_FUNCTION_NONE_APPLICABLE,
            Errors.DELEGATE_PD_METHOD_NONE_APPLICABLE,
        )
    }

    override val token: ValidityToken
        get() = analysisSession.token

    override fun resolveCall(psi: KtElement): KtCallInfo? = with(analysisContext.analyze(psi, AnalysisMode.PARTIAL_WITH_DIAGNOSTICS)) {
        val parentBinaryExpression = psi.parentOfType<KtBinaryExpression>()
        val lhs = KtPsiUtil.deparenthesize(parentBinaryExpression?.left)
        val unwrappedPsi = KtPsiUtil.deparenthesize(psi as? KtExpression) ?: psi
        if (parentBinaryExpression != null &&
            parentBinaryExpression.operationToken == KtTokens.EQ &&
            (lhs == unwrappedPsi || (lhs as? KtQualifiedExpression)?.selectorExpression == unwrappedPsi) &&
            unwrappedPsi !is KtArrayAccessExpression
        ) {
            // Specially handle property assignment because FE1.0 resolves LHS of assignment to just the property, which would then be
            // treated as a property read.
            return resolveCall(parentBinaryExpression)
        }
        when (unwrappedPsi) {
            is KtBinaryExpression -> {
                handleAsCompoundAssignment(unwrappedPsi)?.let { return@with it }
                handleAsFunctionCall(unwrappedPsi)
            }
            is KtUnaryExpression -> {
                handleAsIncOrDecOperator(unwrappedPsi)?.let { return@with it }
                handleAsFunctionCall(unwrappedPsi)
            }
            else -> handleAsFunctionCall(unwrappedPsi) ?: handleAsPropertyRead(unwrappedPsi)
        } ?: handleResolveErrors(psi)
    }

    private fun BindingContext.handleAsCompoundAssignment(binaryExpression: KtBinaryExpression): KtCallInfo? {
        val left = binaryExpression.left ?: return null
        val right = binaryExpression.right
        val resolvedCalls = mutableListOf<ResolvedCall<*>>()
        return when (binaryExpression.operationToken) {
            KtTokens.EQ -> {
                val resolvedCall = left.getResolvedCall(this) ?: return null
                resolvedCalls += resolvedCall
                val partiallyAppliedSymbol =
                    resolvedCall.toPartiallyAppliedVariableSymbol(this) ?: return null
                KtSimpleVariableAccessCall(partiallyAppliedSymbol, KtSimpleVariableAccess.Write(right))
            }
            in KtTokens.AUGMENTED_ASSIGNMENTS -> {
                if (right == null) return null
                val operatorCall = binaryExpression.getResolvedCall(this) ?: return null
                resolvedCalls += operatorCall
                // This method only handles compound assignment. Other cases like `plusAssign`, `rangeTo`, `contains` are handled by plain
                // `handleAsFunctionCall`
                if (operatorCall.resultingDescriptor.name !in operatorWithAssignmentVariant) return null
                val operatorPartiallyAppliedSymbol =
                    operatorCall.toPartiallyAppliedFunctionSymbol<KtFunctionSymbol>(this) ?: return null

                val compoundAccess = KtCompoundAccess.CompoundAssign(
                    operatorPartiallyAppliedSymbol,
                    binaryExpression.getCompoundAssignKind(),
                    right
                )

                if (left is KtArrayAccessExpression) {
                    createCompoundArrayAccessCall(left, compoundAccess, resolvedCalls)
                } else {
                    val resolvedCall = left.getResolvedCall(this) ?: return null
                    resolvedCalls += resolvedCall
                    val variableAppliedSymbol = resolvedCall.toPartiallyAppliedVariableSymbol(this) ?: return null
                    KtCompoundVariableAccessCall(variableAppliedSymbol, compoundAccess)
                }
            }
            else -> null
        }?.let { createCalInfo(binaryExpression, it, resolvedCalls) }
    }

    private fun BindingContext.handleAsIncOrDecOperator(unaryExpression: KtUnaryExpression): KtCallInfo? {
        if (unaryExpression.operationToken !in KtTokens.INCREMENT_AND_DECREMENT) return null
        val operatorCall = unaryExpression.getResolvedCall(this) ?: return null
        val resolvedCalls = mutableListOf(operatorCall)
        val operatorPartiallyAppliedSymbol = operatorCall.toPartiallyAppliedFunctionSymbol<KtFunctionSymbol>(this) ?: return null
        val baseExpression = unaryExpression.baseExpression
        val kind = unaryExpression.getInOrDecOperationKind()
        val precedence = when (unaryExpression) {
            is KtPostfixExpression -> KtCompoundAccess.IncOrDecOperation.Precedence.POSTFIX
            is KtPrefixExpression -> KtCompoundAccess.IncOrDecOperation.Precedence.PREFIX
            else -> error("unexpected KtUnaryExpression $unaryExpression")
        }
        val compoundAccess = KtCompoundAccess.IncOrDecOperation(operatorPartiallyAppliedSymbol, kind, precedence)
        return if (baseExpression is KtArrayAccessExpression) {
            createCompoundArrayAccessCall(baseExpression, compoundAccess, resolvedCalls)
        } else {
            val variableAppliedSymbol = baseExpression.getResolvedCall(this)?.toPartiallyAppliedVariableSymbol(this) ?: return null
            KtCompoundVariableAccessCall(variableAppliedSymbol, compoundAccess)
        }?.let { createCalInfo(unaryExpression, it, resolvedCalls) }
    }

    private fun BindingContext.createCompoundArrayAccessCall(
        arrayAccessExpression: KtArrayAccessExpression,
        compoundAccess: KtCompoundAccess,
        resolvedCalls: MutableList<ResolvedCall<*>>
    ): KtCompoundArrayAccessCall? {
        val resolvedGetCall = this[BindingContext.INDEXED_LVALUE_GET, arrayAccessExpression] ?: return null
        resolvedCalls += resolvedGetCall
        val getPartiallyAppliedSymbol = resolvedGetCall.toPartiallyAppliedFunctionSymbol<KtFunctionSymbol>(this) ?: return null
        val resolvedSetCall = this[BindingContext.INDEXED_LVALUE_SET, arrayAccessExpression] ?: return null
        resolvedCalls += resolvedSetCall
        val setPartiallyAppliedSymbol = resolvedSetCall.toPartiallyAppliedFunctionSymbol<KtFunctionSymbol>(this) ?: return null
        return KtCompoundArrayAccessCall(
            compoundAccess,
            arrayAccessExpression.indexExpressions,
            getPartiallyAppliedSymbol,
            setPartiallyAppliedSymbol
        )
    }

    private fun BindingContext.handleAsFunctionCall(element: KtElement): KtCallInfo? {
        val resolvedCall = element.getResolvedCall(this)
        if (element is KtUnaryExpression && resolvedCall?.candidateDescriptor?.name == ControlStructureTypingUtils.ResolveConstruct.EXCL_EXCL.specialFunctionName) {
            val baseExpression = element.baseExpression ?: return null
            return KtSuccessCallInfo(KtCheckNotNullCall(token, baseExpression))
        }
        return if (resolvedCall is VariableAsFunctionResolvedCall) {
            if (element is KtCallExpression) {
                resolvedCall.functionCall.toFunctionKtCall(this)
            } else {
                resolvedCall.variableCall.toPropertyRead(this)
            }?.let { createCalInfo(element, it, listOf(resolvedCall)) }
        } else {
            resolvedCall?.toFunctionKtCall(this)?.let { createCalInfo(element, it, listOf(resolvedCall)) }
        }
    }

    private fun BindingContext.handleAsPropertyRead(element: KtElement): KtCallInfo? {
        val call = element.getResolvedCall(this) ?: return null
        return call.toPropertyRead(this)?.let { createCalInfo(element, it, listOf(call)) }
    }

    private fun ResolvedCall<*>.toPropertyRead(context: BindingContext): KtVariableAccessCall? {
        val partiallyAppliedSymbol = toPartiallyAppliedVariableSymbol(context) ?: return null
        return KtSimpleVariableAccessCall(partiallyAppliedSymbol, KtSimpleVariableAccess.Read)
    }

    private fun ResolvedCall<*>.toFunctionKtCall(context: BindingContext): KtFunctionCall<*>? {
        val partiallyAppliedSymbol = toPartiallyAppliedFunctionSymbol<KtFunctionLikeSymbol>(context) ?: return null
        val argumentMapping = createArgumentMapping(partiallyAppliedSymbol.signature)
        if (partiallyAppliedSymbol.signature.symbol is KtConstructorSymbol) {
            @Suppress("UNCHECKED_CAST")
            val partiallyAppliedConstructorSymbol = partiallyAppliedSymbol as KtPartiallyAppliedFunctionSymbol<KtConstructorSymbol>
            when (val callElement = call.callElement) {
                is KtAnnotationEntry -> return KtAnnotationCall(partiallyAppliedSymbol, argumentMapping)
                is KtConstructorDelegationCall -> return KtDelegatedConstructorCall(
                    partiallyAppliedConstructorSymbol,
                    if (callElement.isCallToThis) KtDelegatedConstructorCall.Kind.THIS_CALL else KtDelegatedConstructorCall.Kind.SUPER_CALL,
                    argumentMapping
                )
            }
        }
        @Suppress("UNCHECKED_CAST")
        return KtSimpleFunctionCall(partiallyAppliedSymbol, argumentMapping, call.callType == Call.CallType.INVOKE)
    }

    private fun ResolvedCall<*>.toPartiallyAppliedVariableSymbol(context: BindingContext): KtPartiallyAppliedVariableSymbol<KtVariableLikeSymbol>? {
        val partiallyAppliedSymbol = toPartiallyAppliedSymbol(context) ?: return null
        if (partiallyAppliedSymbol.signature !is KtVariableLikeSignature<*>) return null
        @Suppress("UNCHECKED_CAST")
        return partiallyAppliedSymbol as KtPartiallyAppliedVariableSymbol<KtVariableLikeSymbol>
    }


    private inline fun <reified S : KtFunctionLikeSymbol> ResolvedCall<*>.toPartiallyAppliedFunctionSymbol(context: BindingContext): KtPartiallyAppliedFunctionSymbol<S>? {
        val partiallyAppliedSymbol = toPartiallyAppliedSymbol(context) ?: return null
        if (partiallyAppliedSymbol.symbol !is S) return null
        @Suppress("UNCHECKED_CAST")
        return partiallyAppliedSymbol as KtPartiallyAppliedFunctionSymbol<S>
    }

    private fun ResolvedCall<*>.toPartiallyAppliedSymbol(context: BindingContext): KtPartiallyAppliedSymbol<*, *>? {
        val targetDescriptor = candidateDescriptor
        val symbol = targetDescriptor.toKtCallableSymbol(analysisContext) ?: return null
        val signature = createSignature(symbol, resultingDescriptor) ?: return null
        if (targetDescriptor.isSynthesizedPropertyFromJavaAccessors()) {
            // FE1.0 represents synthesized properties as an extension property of the Java class. Hence we use the extension receiver as
            // the dispatch receiver and always pass null for extension receiver (because in Java there is no way to specify an extension
            // receiver)
            return KtPartiallyAppliedSymbol(
                signature,
                extensionReceiver?.toKtReceiverValue(context, this),
                null
            )
        } else {
            return KtPartiallyAppliedSymbol(
                signature,
                dispatchReceiver?.toKtReceiverValue(context, this, smartCastDispatchReceiverType),
                extensionReceiver?.toKtReceiverValue(context, this),
            )
        }
    }

    private fun ReceiverValue.toKtReceiverValue(
        context: BindingContext,
        resolvedCall: ResolvedCall<*>,
        smartCastType: KotlinType? = null
    ): KtReceiverValue? {
        val result = when (this) {
            is ExpressionReceiver -> expression.toExplicitReceiverValue()
            is ExtensionReceiver -> {
                val extensionReceiverParameter = this.declarationDescriptor.extensionReceiverParameter ?: return null
                KtImplicitReceiverValue(KtFe10ReceiverParameterSymbol(extensionReceiverParameter, analysisContext))
            }
            is ImplicitReceiver -> {
                val symbol = this.declarationDescriptor.toKtSymbol(analysisContext) ?: return null
                KtImplicitReceiverValue(symbol)
            }
            else -> null
        }
        var smartCastTypeToUse = smartCastType
        if (smartCastTypeToUse == null) {
            when (result) {
                is KtExplicitReceiverValue -> {
                    smartCastTypeToUse = context[BindingContext.SMARTCAST, result.expression]?.type(resolvedCall.call)
                }
                is KtImplicitReceiverValue -> {
                    smartCastTypeToUse =
                        context[BindingContext.IMPLICIT_RECEIVER_SMARTCAST, resolvedCall.call.calleeExpression]?.receiverTypes?.get(this)
                }
                else -> {}
            }
        }
        return if (smartCastTypeToUse != null && result != null) {
            KtSmartCastedReceiverValue(result, smartCastTypeToUse.toKtType(analysisContext))
        } else {
            result
        }
    }

    private fun createSignature(symbol: KtSymbol, resultingDescriptor: CallableDescriptor): KtSignature<*>? {
        val returnType = if (resultingDescriptor is ValueParameterDescriptor && resultingDescriptor.isVararg) {
            val arrayType = resultingDescriptor.returnType ?: return null
            val primitiveArrayElementType = KotlinBuiltIns.getPrimitiveArrayElementType(arrayType)
            if (primitiveArrayElementType == null) {
                arrayType.arguments.singleOrNull()?.type
            } else {
                analysisContext.builtIns.getPrimitiveKotlinType(primitiveArrayElementType)
            }
        } else {
            resultingDescriptor.returnType
        }
        val ktReturnType = returnType?.toKtType(analysisContext) ?: return null
        val receiverType = if (resultingDescriptor.isSynthesizedPropertyFromJavaAccessors()) {
            // FE1.0 represents synthesized properties as an extension property of the Java class. Hence the extension receiver type should
            // always be null
            null
        } else {
            resultingDescriptor.extensionReceiverParameter?.returnType?.toKtType(analysisContext)
        }
        return when (symbol) {
            is KtVariableLikeSymbol -> KtVariableLikeSignature(symbol, ktReturnType, receiverType)
            is KtFunctionLikeSymbol -> KtFunctionLikeSignature(
                symbol,
                ktReturnType,
                receiverType,
                @Suppress("UNCHECKED_CAST")
                symbol.valueParameters.zip(resultingDescriptor.valueParameters).map { (symbol, resultingDescriptor) ->
                    createSignature(symbol, resultingDescriptor) as KtVariableLikeSignature<KtValueParameterSymbol>
                })
            else -> error("unexpected callable symbol $this")
        }
    }

    private fun CallableDescriptor?.isSynthesizedPropertyFromJavaAccessors() =
        this is PropertyDescriptor && kind == CallableMemberDescriptor.Kind.SYNTHESIZED

    private fun ResolvedCall<*>.createArgumentMapping(signature: KtFunctionLikeSignature<*>): LinkedHashMap<KtExpression, KtVariableLikeSignature<KtValueParameterSymbol>> {
        val parameterSignatureByName = signature.valueParameters.associateBy { it.symbol.name }
        val result = LinkedHashMap<KtExpression, KtVariableLikeSignature<KtValueParameterSymbol>>()
        for ((parameter, arguments) in valueArguments) {
            val parameterSymbol = KtFe10DescValueParameterSymbol(parameter, analysisContext)

            for (argument in arguments.arguments) {
                val expression = argument.getArgumentExpression() ?: continue
                result[expression] = parameterSignatureByName[parameterSymbol.name] ?: continue
            }
        }
        return result
    }

    private fun BindingContext.createCalInfo(psi: KtElement, ktCall: KtCall, resolvedCalls: List<ResolvedCall<*>>): KtCallInfo {
        val failedResolveCall = resolvedCalls.firstOrNull { !it.status.isSuccess } ?: return KtSuccessCallInfo(ktCall)

        val diagnostic = getDiagnosticToReport(psi, ktCall)?.let { KtFe10Diagnostic(it, token) }
            ?: KtNonBoundToPsiErrorDiagnostic(
                factoryName = null,
                "${failedResolveCall.status} with ${failedResolveCall.resultingDescriptor.name}",
                token
            )
        return KtErrorCallInfo(listOf(ktCall), diagnostic, token)
    }

    private fun BindingContext.handleResolveErrors(psi: KtElement): KtErrorCallInfo? {
        val diagnostic = getDiagnosticToReport(psi, null) ?: return null
        val ktDiagnostic = diagnostic.let { KtFe10Diagnostic(it, token) }
        val calls = when (diagnostic.factory) {
            in diagnosticWithResolvedCallsAtPosition1 -> {
                require(diagnostic is DiagnosticWithParameters1<*, *>)
                @Suppress("UNCHECKED_CAST")
                diagnostic.a as Collection<ResolvedCall<*>>
            }
            in diagnosticWithResolvedCallsAtPosition2 -> {
                require(diagnostic is DiagnosticWithParameters2<*, *, *>)
                @Suppress("UNCHECKED_CAST")
                diagnostic.b as Collection<ResolvedCall<*>>
            }
            else -> {
                emptyList()
            }
        }
        return KtErrorCallInfo(calls.mapNotNull { it.toFunctionKtCall(this) ?: it.toPropertyRead(this) }, ktDiagnostic, token)
    }

    private fun BindingContext.getDiagnosticToReport(psi: KtElement, ktCall: KtCall?) = diagnostics.firstOrNull { diagnostic ->
        if (diagnostic.severity != Severity.ERROR) return@firstOrNull false
        val isResolutionError = diagnostic.factory in resolutionFailureErrors
        val isCallArgError = diagnostic.factory in callArgErrors
        val reportedPsi = diagnostic.psiElement
        val reportedPsiParent = reportedPsi.parent
        when {
            // Errors reported on the querying element or the `selectorExpression`/`calleeExpression` of the querying element
            isResolutionError &&
                    (reportedPsi == psi ||
                            psi is KtQualifiedExpression && reportedPsi == psi.selectorExpression ||
                            psi is KtCallElement && reportedPsi.parentsWithSelf.any { it == psi.calleeExpression }) -> true
            // Errors reported on the value argument list or the right most parentheses (not enough argument, for example)
            isResolutionError &&
                    reportedPsi is KtValueArgumentList || reportedPsiParent is KtValueArgumentList && reportedPsi == reportedPsiParent.rightParenthesis -> true
            // errors on call args for normal function calls
            isCallArgError &&
                    reportedPsiParent is KtValueArgument && psi is KtCallElement && reportedPsiParent in psi.valueArguments -> true
            // errors on index args for array access convention
            isCallArgError &&
                    reportedPsiParent is KtContainerNode && reportedPsiParent.parent is KtArrayAccessExpression -> true
            // errors on lambda args
            isCallArgError &&
                    reportedPsi is KtLambdaExpression || reportedPsi is KtLambdaArgument -> true
            // errors on value to set using array access convention
            isCallArgError &&
                    ktCall is KtSimpleFunctionCall && (reportedPsiParent as? KtBinaryExpression)?.right == reportedPsi -> true
            else -> false
        }
    }
}