(function (global, factory) {
  typeof exports === 'object' && typeof module !== 'undefined' ? module.exports = factory(require('react'), require('@emotion/core'), require('react-dom')) :
  typeof define === 'function' && define.amd ? define(['react', '@emotion/core', 'react-dom'], factory) :
  (global = global || self, global.reactSampleComponentsLibrary = factory(global.React, global.core, global.reactDom));
}(this, (function (React, core, reactDom) { 'use strict';

  var React__default = 'default' in React ? React['default'] : React;

  function _defineProperty(obj, key, value) {
    if (key in obj) {
      Object.defineProperty(obj, key, {
        value: value,
        enumerable: true,
        configurable: true,
        writable: true
      });
    } else {
      obj[key] = value;
    }

    return obj;
  }

  function _extends() {
    _extends = Object.assign || function (target) {
      for (var i = 1; i < arguments.length; i++) {
        var source = arguments[i];

        for (var key in source) {
          if (Object.prototype.hasOwnProperty.call(source, key)) {
            target[key] = source[key];
          }
        }
      }

      return target;
    };

    return _extends.apply(this, arguments);
  }

  function ownKeys(object, enumerableOnly) {
    var keys = Object.keys(object);

    if (Object.getOwnPropertySymbols) {
      var symbols = Object.getOwnPropertySymbols(object);
      if (enumerableOnly) symbols = symbols.filter(function (sym) {
        return Object.getOwnPropertyDescriptor(object, sym).enumerable;
      });
      keys.push.apply(keys, symbols);
    }

    return keys;
  }

  function _objectSpread2(target) {
    for (var i = 1; i < arguments.length; i++) {
      var source = arguments[i] != null ? arguments[i] : {};

      if (i % 2) {
        ownKeys(Object(source), true).forEach(function (key) {
          _defineProperty(target, key, source[key]);
        });
      } else if (Object.getOwnPropertyDescriptors) {
        Object.defineProperties(target, Object.getOwnPropertyDescriptors(source));
      } else {
        ownKeys(Object(source)).forEach(function (key) {
          Object.defineProperty(target, key, Object.getOwnPropertyDescriptor(source, key));
        });
      }
    }

    return target;
  }

  function areInputsEqual(newInputs, lastInputs) {
      if (newInputs.length !== lastInputs.length) {
          return false;
      }
      for (var i = 0; i < newInputs.length; i++) {
          if (newInputs[i] !== lastInputs[i]) {
              return false;
          }
      }
      return true;
  }

  function memoizeOne(resultFn, isEqual) {
      if (isEqual === void 0) { isEqual = areInputsEqual; }
      var lastThis;
      var lastArgs = [];
      var lastResult;
      var calledOnce = false;
      function memoized() {
          var newArgs = [];
          for (var _i = 0; _i < arguments.length; _i++) {
              newArgs[_i] = arguments[_i];
          }
          if (calledOnce && lastThis === this && isEqual(newArgs, lastArgs)) {
              return lastResult;
          }
          lastResult = resultFn.apply(this, newArgs);
          calledOnce = true;
          lastThis = this;
          lastArgs = newArgs;
          return lastResult;
      }
      return memoized;
  }

  function unwrapExports (x) {
  	return x && x.__esModule && Object.prototype.hasOwnProperty.call(x, 'default') ? x['default'] : x;
  }

  function createCommonjsModule(fn, module) {
  	return module = { exports: {} }, fn(module, module.exports), module.exports;
  }

  /** @license React v16.13.1
   * react-is.production.min.js
   *
   * Copyright (c) Facebook, Inc. and its affiliates.
   *
   * This source code is licensed under the MIT license found in the
   * LICENSE file in the root directory of this source tree.
   */
  var b="function"===typeof Symbol&&Symbol.for,c=b?Symbol.for("react.element"):60103,d=b?Symbol.for("react.portal"):60106,e=b?Symbol.for("react.fragment"):60107,f=b?Symbol.for("react.strict_mode"):60108,g=b?Symbol.for("react.profiler"):60114,h=b?Symbol.for("react.provider"):60109,k=b?Symbol.for("react.context"):60110,l=b?Symbol.for("react.async_mode"):60111,m=b?Symbol.for("react.concurrent_mode"):60111,n=b?Symbol.for("react.forward_ref"):60112,p=b?Symbol.for("react.suspense"):60113,q=b?
  Symbol.for("react.suspense_list"):60120,r=b?Symbol.for("react.memo"):60115,t=b?Symbol.for("react.lazy"):60116,v=b?Symbol.for("react.block"):60121,w=b?Symbol.for("react.fundamental"):60117,x=b?Symbol.for("react.responder"):60118,y=b?Symbol.for("react.scope"):60119;
  function z(a){if("object"===typeof a&&null!==a){var u=a.$$typeof;switch(u){case c:switch(a=a.type,a){case l:case m:case e:case g:case f:case p:return a;default:switch(a=a&&a.$$typeof,a){case k:case n:case t:case r:case h:return a;default:return u}}case d:return u}}}function A(a){return z(a)===m}var AsyncMode=l;var ConcurrentMode=m;var ContextConsumer=k;var ContextProvider=h;var Element=c;var ForwardRef=n;var Fragment=e;var Lazy=t;var Memo=r;var Portal=d;
  var Profiler=g;var StrictMode=f;var Suspense=p;var isAsyncMode=function(a){return A(a)||z(a)===l};var isConcurrentMode=A;var isContextConsumer=function(a){return z(a)===k};var isContextProvider=function(a){return z(a)===h};var isElement=function(a){return "object"===typeof a&&null!==a&&a.$$typeof===c};var isForwardRef=function(a){return z(a)===n};var isFragment=function(a){return z(a)===e};var isLazy=function(a){return z(a)===t};
  var isMemo=function(a){return z(a)===r};var isPortal=function(a){return z(a)===d};var isProfiler=function(a){return z(a)===g};var isStrictMode=function(a){return z(a)===f};var isSuspense=function(a){return z(a)===p};
  var isValidElementType=function(a){return "string"===typeof a||"function"===typeof a||a===e||a===m||a===g||a===f||a===p||a===q||"object"===typeof a&&null!==a&&(a.$$typeof===t||a.$$typeof===r||a.$$typeof===h||a.$$typeof===k||a.$$typeof===n||a.$$typeof===w||a.$$typeof===x||a.$$typeof===y||a.$$typeof===v)};var typeOf=z;

  var reactIs_production_min = {
  	AsyncMode: AsyncMode,
  	ConcurrentMode: ConcurrentMode,
  	ContextConsumer: ContextConsumer,
  	ContextProvider: ContextProvider,
  	Element: Element,
  	ForwardRef: ForwardRef,
  	Fragment: Fragment,
  	Lazy: Lazy,
  	Memo: Memo,
  	Portal: Portal,
  	Profiler: Profiler,
  	StrictMode: StrictMode,
  	Suspense: Suspense,
  	isAsyncMode: isAsyncMode,
  	isConcurrentMode: isConcurrentMode,
  	isContextConsumer: isContextConsumer,
  	isContextProvider: isContextProvider,
  	isElement: isElement,
  	isForwardRef: isForwardRef,
  	isFragment: isFragment,
  	isLazy: isLazy,
  	isMemo: isMemo,
  	isPortal: isPortal,
  	isProfiler: isProfiler,
  	isStrictMode: isStrictMode,
  	isSuspense: isSuspense,
  	isValidElementType: isValidElementType,
  	typeOf: typeOf
  };

  var reactIs_development = createCommonjsModule(function (module, exports) {



  if (process.env.NODE_ENV !== "production") {
    (function() {

  // The Symbol used to tag the ReactElement-like types. If there is no native Symbol
  // nor polyfill, then a plain number is used for performance.
  var hasSymbol = typeof Symbol === 'function' && Symbol.for;
  var REACT_ELEMENT_TYPE = hasSymbol ? Symbol.for('react.element') : 0xeac7;
  var REACT_PORTAL_TYPE = hasSymbol ? Symbol.for('react.portal') : 0xeaca;
  var REACT_FRAGMENT_TYPE = hasSymbol ? Symbol.for('react.fragment') : 0xeacb;
  var REACT_STRICT_MODE_TYPE = hasSymbol ? Symbol.for('react.strict_mode') : 0xeacc;
  var REACT_PROFILER_TYPE = hasSymbol ? Symbol.for('react.profiler') : 0xead2;
  var REACT_PROVIDER_TYPE = hasSymbol ? Symbol.for('react.provider') : 0xeacd;
  var REACT_CONTEXT_TYPE = hasSymbol ? Symbol.for('react.context') : 0xeace; // TODO: We don't use AsyncMode or ConcurrentMode anymore. They were temporary
  // (unstable) APIs that have been removed. Can we remove the symbols?

  var REACT_ASYNC_MODE_TYPE = hasSymbol ? Symbol.for('react.async_mode') : 0xeacf;
  var REACT_CONCURRENT_MODE_TYPE = hasSymbol ? Symbol.for('react.concurrent_mode') : 0xeacf;
  var REACT_FORWARD_REF_TYPE = hasSymbol ? Symbol.for('react.forward_ref') : 0xead0;
  var REACT_SUSPENSE_TYPE = hasSymbol ? Symbol.for('react.suspense') : 0xead1;
  var REACT_SUSPENSE_LIST_TYPE = hasSymbol ? Symbol.for('react.suspense_list') : 0xead8;
  var REACT_MEMO_TYPE = hasSymbol ? Symbol.for('react.memo') : 0xead3;
  var REACT_LAZY_TYPE = hasSymbol ? Symbol.for('react.lazy') : 0xead4;
  var REACT_BLOCK_TYPE = hasSymbol ? Symbol.for('react.block') : 0xead9;
  var REACT_FUNDAMENTAL_TYPE = hasSymbol ? Symbol.for('react.fundamental') : 0xead5;
  var REACT_RESPONDER_TYPE = hasSymbol ? Symbol.for('react.responder') : 0xead6;
  var REACT_SCOPE_TYPE = hasSymbol ? Symbol.for('react.scope') : 0xead7;

  function isValidElementType(type) {
    return typeof type === 'string' || typeof type === 'function' || // Note: its typeof might be other than 'symbol' or 'number' if it's a polyfill.
    type === REACT_FRAGMENT_TYPE || type === REACT_CONCURRENT_MODE_TYPE || type === REACT_PROFILER_TYPE || type === REACT_STRICT_MODE_TYPE || type === REACT_SUSPENSE_TYPE || type === REACT_SUSPENSE_LIST_TYPE || typeof type === 'object' && type !== null && (type.$$typeof === REACT_LAZY_TYPE || type.$$typeof === REACT_MEMO_TYPE || type.$$typeof === REACT_PROVIDER_TYPE || type.$$typeof === REACT_CONTEXT_TYPE || type.$$typeof === REACT_FORWARD_REF_TYPE || type.$$typeof === REACT_FUNDAMENTAL_TYPE || type.$$typeof === REACT_RESPONDER_TYPE || type.$$typeof === REACT_SCOPE_TYPE || type.$$typeof === REACT_BLOCK_TYPE);
  }

  function typeOf(object) {
    if (typeof object === 'object' && object !== null) {
      var $$typeof = object.$$typeof;

      switch ($$typeof) {
        case REACT_ELEMENT_TYPE:
          var type = object.type;

          switch (type) {
            case REACT_ASYNC_MODE_TYPE:
            case REACT_CONCURRENT_MODE_TYPE:
            case REACT_FRAGMENT_TYPE:
            case REACT_PROFILER_TYPE:
            case REACT_STRICT_MODE_TYPE:
            case REACT_SUSPENSE_TYPE:
              return type;

            default:
              var $$typeofType = type && type.$$typeof;

              switch ($$typeofType) {
                case REACT_CONTEXT_TYPE:
                case REACT_FORWARD_REF_TYPE:
                case REACT_LAZY_TYPE:
                case REACT_MEMO_TYPE:
                case REACT_PROVIDER_TYPE:
                  return $$typeofType;

                default:
                  return $$typeof;
              }

          }

        case REACT_PORTAL_TYPE:
          return $$typeof;
      }
    }

    return undefined;
  } // AsyncMode is deprecated along with isAsyncMode

  var AsyncMode = REACT_ASYNC_MODE_TYPE;
  var ConcurrentMode = REACT_CONCURRENT_MODE_TYPE;
  var ContextConsumer = REACT_CONTEXT_TYPE;
  var ContextProvider = REACT_PROVIDER_TYPE;
  var Element = REACT_ELEMENT_TYPE;
  var ForwardRef = REACT_FORWARD_REF_TYPE;
  var Fragment = REACT_FRAGMENT_TYPE;
  var Lazy = REACT_LAZY_TYPE;
  var Memo = REACT_MEMO_TYPE;
  var Portal = REACT_PORTAL_TYPE;
  var Profiler = REACT_PROFILER_TYPE;
  var StrictMode = REACT_STRICT_MODE_TYPE;
  var Suspense = REACT_SUSPENSE_TYPE;
  var hasWarnedAboutDeprecatedIsAsyncMode = false; // AsyncMode should be deprecated

  function isAsyncMode(object) {
    {
      if (!hasWarnedAboutDeprecatedIsAsyncMode) {
        hasWarnedAboutDeprecatedIsAsyncMode = true; // Using console['warn'] to evade Babel and ESLint

        console['warn']('The ReactIs.isAsyncMode() alias has been deprecated, ' + 'and will be removed in React 17+. Update your code to use ' + 'ReactIs.isConcurrentMode() instead. It has the exact same API.');
      }
    }

    return isConcurrentMode(object) || typeOf(object) === REACT_ASYNC_MODE_TYPE;
  }
  function isConcurrentMode(object) {
    return typeOf(object) === REACT_CONCURRENT_MODE_TYPE;
  }
  function isContextConsumer(object) {
    return typeOf(object) === REACT_CONTEXT_TYPE;
  }
  function isContextProvider(object) {
    return typeOf(object) === REACT_PROVIDER_TYPE;
  }
  function isElement(object) {
    return typeof object === 'object' && object !== null && object.$$typeof === REACT_ELEMENT_TYPE;
  }
  function isForwardRef(object) {
    return typeOf(object) === REACT_FORWARD_REF_TYPE;
  }
  function isFragment(object) {
    return typeOf(object) === REACT_FRAGMENT_TYPE;
  }
  function isLazy(object) {
    return typeOf(object) === REACT_LAZY_TYPE;
  }
  function isMemo(object) {
    return typeOf(object) === REACT_MEMO_TYPE;
  }
  function isPortal(object) {
    return typeOf(object) === REACT_PORTAL_TYPE;
  }
  function isProfiler(object) {
    return typeOf(object) === REACT_PROFILER_TYPE;
  }
  function isStrictMode(object) {
    return typeOf(object) === REACT_STRICT_MODE_TYPE;
  }
  function isSuspense(object) {
    return typeOf(object) === REACT_SUSPENSE_TYPE;
  }

  exports.AsyncMode = AsyncMode;
  exports.ConcurrentMode = ConcurrentMode;
  exports.ContextConsumer = ContextConsumer;
  exports.ContextProvider = ContextProvider;
  exports.Element = Element;
  exports.ForwardRef = ForwardRef;
  exports.Fragment = Fragment;
  exports.Lazy = Lazy;
  exports.Memo = Memo;
  exports.Portal = Portal;
  exports.Profiler = Profiler;
  exports.StrictMode = StrictMode;
  exports.Suspense = Suspense;
  exports.isAsyncMode = isAsyncMode;
  exports.isConcurrentMode = isConcurrentMode;
  exports.isContextConsumer = isContextConsumer;
  exports.isContextProvider = isContextProvider;
  exports.isElement = isElement;
  exports.isForwardRef = isForwardRef;
  exports.isFragment = isFragment;
  exports.isLazy = isLazy;
  exports.isMemo = isMemo;
  exports.isPortal = isPortal;
  exports.isProfiler = isProfiler;
  exports.isStrictMode = isStrictMode;
  exports.isSuspense = isSuspense;
  exports.isValidElementType = isValidElementType;
  exports.typeOf = typeOf;
    })();
  }
  });
  var reactIs_development_1 = reactIs_development.AsyncMode;
  var reactIs_development_2 = reactIs_development.ConcurrentMode;
  var reactIs_development_3 = reactIs_development.ContextConsumer;
  var reactIs_development_4 = reactIs_development.ContextProvider;
  var reactIs_development_5 = reactIs_development.Element;
  var reactIs_development_6 = reactIs_development.ForwardRef;
  var reactIs_development_7 = reactIs_development.Fragment;
  var reactIs_development_8 = reactIs_development.Lazy;
  var reactIs_development_9 = reactIs_development.Memo;
  var reactIs_development_10 = reactIs_development.Portal;
  var reactIs_development_11 = reactIs_development.Profiler;
  var reactIs_development_12 = reactIs_development.StrictMode;
  var reactIs_development_13 = reactIs_development.Suspense;
  var reactIs_development_14 = reactIs_development.isAsyncMode;
  var reactIs_development_15 = reactIs_development.isConcurrentMode;
  var reactIs_development_16 = reactIs_development.isContextConsumer;
  var reactIs_development_17 = reactIs_development.isContextProvider;
  var reactIs_development_18 = reactIs_development.isElement;
  var reactIs_development_19 = reactIs_development.isForwardRef;
  var reactIs_development_20 = reactIs_development.isFragment;
  var reactIs_development_21 = reactIs_development.isLazy;
  var reactIs_development_22 = reactIs_development.isMemo;
  var reactIs_development_23 = reactIs_development.isPortal;
  var reactIs_development_24 = reactIs_development.isProfiler;
  var reactIs_development_25 = reactIs_development.isStrictMode;
  var reactIs_development_26 = reactIs_development.isSuspense;
  var reactIs_development_27 = reactIs_development.isValidElementType;
  var reactIs_development_28 = reactIs_development.typeOf;

  var reactIs = createCommonjsModule(function (module) {

  if (process.env.NODE_ENV === 'production') {
    module.exports = reactIs_production_min;
  } else {
    module.exports = reactIs_development;
  }
  });

  /*
  object-assign
  (c) Sindre Sorhus
  @license MIT
  */
  /* eslint-disable no-unused-vars */
  var getOwnPropertySymbols = Object.getOwnPropertySymbols;
  var hasOwnProperty = Object.prototype.hasOwnProperty;
  var propIsEnumerable = Object.prototype.propertyIsEnumerable;

  function toObject(val) {
  	if (val === null || val === undefined) {
  		throw new TypeError('Object.assign cannot be called with null or undefined');
  	}

  	return Object(val);
  }

  function shouldUseNative() {
  	try {
  		if (!Object.assign) {
  			return false;
  		}

  		// Detect buggy property enumeration order in older V8 versions.

  		// https://bugs.chromium.org/p/v8/issues/detail?id=4118
  		var test1 = new String('abc');  // eslint-disable-line no-new-wrappers
  		test1[5] = 'de';
  		if (Object.getOwnPropertyNames(test1)[0] === '5') {
  			return false;
  		}

  		// https://bugs.chromium.org/p/v8/issues/detail?id=3056
  		var test2 = {};
  		for (var i = 0; i < 10; i++) {
  			test2['_' + String.fromCharCode(i)] = i;
  		}
  		var order2 = Object.getOwnPropertyNames(test2).map(function (n) {
  			return test2[n];
  		});
  		if (order2.join('') !== '0123456789') {
  			return false;
  		}

  		// https://bugs.chromium.org/p/v8/issues/detail?id=3056
  		var test3 = {};
  		'abcdefghijklmnopqrst'.split('').forEach(function (letter) {
  			test3[letter] = letter;
  		});
  		if (Object.keys(Object.assign({}, test3)).join('') !==
  				'abcdefghijklmnopqrst') {
  			return false;
  		}

  		return true;
  	} catch (err) {
  		// We don't expect any of the above to throw, but better to be safe.
  		return false;
  	}
  }

  var objectAssign = shouldUseNative() ? Object.assign : function (target, source) {
  	var from;
  	var to = toObject(target);
  	var symbols;

  	for (var s = 1; s < arguments.length; s++) {
  		from = Object(arguments[s]);

  		for (var key in from) {
  			if (hasOwnProperty.call(from, key)) {
  				to[key] = from[key];
  			}
  		}

  		if (getOwnPropertySymbols) {
  			symbols = getOwnPropertySymbols(from);
  			for (var i = 0; i < symbols.length; i++) {
  				if (propIsEnumerable.call(from, symbols[i])) {
  					to[symbols[i]] = from[symbols[i]];
  				}
  			}
  		}
  	}

  	return to;
  };

  /**
   * Copyright (c) 2013-present, Facebook, Inc.
   *
   * This source code is licensed under the MIT license found in the
   * LICENSE file in the root directory of this source tree.
   */

  var ReactPropTypesSecret = 'SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED';

  var ReactPropTypesSecret_1 = ReactPropTypesSecret;

  var printWarning = function() {};

  if (process.env.NODE_ENV !== 'production') {
    var ReactPropTypesSecret$1 = ReactPropTypesSecret_1;
    var loggedTypeFailures = {};
    var has = Function.call.bind(Object.prototype.hasOwnProperty);

    printWarning = function(text) {
      var message = 'Warning: ' + text;
      if (typeof console !== 'undefined') {
        console.error(message);
      }
      try {
        // --- Welcome to debugging React ---
        // This error was thrown as a convenience so that you can use this stack
        // to find the callsite that caused this warning to fire.
        throw new Error(message);
      } catch (x) {}
    };
  }

  /**
   * Assert that the values match with the type specs.
   * Error messages are memorized and will only be shown once.
   *
   * @param {object} typeSpecs Map of name to a ReactPropType
   * @param {object} values Runtime values that need to be type-checked
   * @param {string} location e.g. "prop", "context", "child context"
   * @param {string} componentName Name of the component for error messages.
   * @param {?Function} getStack Returns the component stack.
   * @private
   */
  function checkPropTypes(typeSpecs, values, location, componentName, getStack) {
    if (process.env.NODE_ENV !== 'production') {
      for (var typeSpecName in typeSpecs) {
        if (has(typeSpecs, typeSpecName)) {
          var error;
          // Prop type validation may throw. In case they do, we don't want to
          // fail the render phase where it didn't fail before. So we log it.
          // After these have been cleaned up, we'll let them throw.
          try {
            // This is intentionally an invariant that gets caught. It's the same
            // behavior as without this statement except with a better message.
            if (typeof typeSpecs[typeSpecName] !== 'function') {
              var err = Error(
                (componentName || 'React class') + ': ' + location + ' type `' + typeSpecName + '` is invalid; ' +
                'it must be a function, usually from the `prop-types` package, but received `' + typeof typeSpecs[typeSpecName] + '`.'
              );
              err.name = 'Invariant Violation';
              throw err;
            }
            error = typeSpecs[typeSpecName](values, typeSpecName, componentName, location, null, ReactPropTypesSecret$1);
          } catch (ex) {
            error = ex;
          }
          if (error && !(error instanceof Error)) {
            printWarning(
              (componentName || 'React class') + ': type specification of ' +
              location + ' `' + typeSpecName + '` is invalid; the type checker ' +
              'function must return `null` or an `Error` but returned a ' + typeof error + '. ' +
              'You may have forgotten to pass an argument to the type checker ' +
              'creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and ' +
              'shape all require an argument).'
            );
          }
          if (error instanceof Error && !(error.message in loggedTypeFailures)) {
            // Only monitor this failure once because there tends to be a lot of the
            // same error.
            loggedTypeFailures[error.message] = true;

            var stack = getStack ? getStack() : '';

            printWarning(
              'Failed ' + location + ' type: ' + error.message + (stack != null ? stack : '')
            );
          }
        }
      }
    }
  }

  /**
   * Resets warning cache when testing.
   *
   * @private
   */
  checkPropTypes.resetWarningCache = function() {
    if (process.env.NODE_ENV !== 'production') {
      loggedTypeFailures = {};
    }
  };

  var checkPropTypes_1 = checkPropTypes;

  var has$1 = Function.call.bind(Object.prototype.hasOwnProperty);
  var printWarning$1 = function() {};

  if (process.env.NODE_ENV !== 'production') {
    printWarning$1 = function(text) {
      var message = 'Warning: ' + text;
      if (typeof console !== 'undefined') {
        console.error(message);
      }
      try {
        // --- Welcome to debugging React ---
        // This error was thrown as a convenience so that you can use this stack
        // to find the callsite that caused this warning to fire.
        throw new Error(message);
      } catch (x) {}
    };
  }

  function emptyFunctionThatReturnsNull() {
    return null;
  }

  var factoryWithTypeCheckers = function(isValidElement, throwOnDirectAccess) {
    /* global Symbol */
    var ITERATOR_SYMBOL = typeof Symbol === 'function' && Symbol.iterator;
    var FAUX_ITERATOR_SYMBOL = '@@iterator'; // Before Symbol spec.

    /**
     * Returns the iterator method function contained on the iterable object.
     *
     * Be sure to invoke the function with the iterable as context:
     *
     *     var iteratorFn = getIteratorFn(myIterable);
     *     if (iteratorFn) {
     *       var iterator = iteratorFn.call(myIterable);
     *       ...
     *     }
     *
     * @param {?object} maybeIterable
     * @return {?function}
     */
    function getIteratorFn(maybeIterable) {
      var iteratorFn = maybeIterable && (ITERATOR_SYMBOL && maybeIterable[ITERATOR_SYMBOL] || maybeIterable[FAUX_ITERATOR_SYMBOL]);
      if (typeof iteratorFn === 'function') {
        return iteratorFn;
      }
    }

    /**
     * Collection of methods that allow declaration and validation of props that are
     * supplied to React components. Example usage:
     *
     *   var Props = require('ReactPropTypes');
     *   var MyArticle = React.createClass({
     *     propTypes: {
     *       // An optional string prop named "description".
     *       description: Props.string,
     *
     *       // A required enum prop named "category".
     *       category: Props.oneOf(['News','Photos']).isRequired,
     *
     *       // A prop named "dialog" that requires an instance of Dialog.
     *       dialog: Props.instanceOf(Dialog).isRequired
     *     },
     *     render: function() { ... }
     *   });
     *
     * A more formal specification of how these methods are used:
     *
     *   type := array|bool|func|object|number|string|oneOf([...])|instanceOf(...)
     *   decl := ReactPropTypes.{type}(.isRequired)?
     *
     * Each and every declaration produces a function with the same signature. This
     * allows the creation of custom validation functions. For example:
     *
     *  var MyLink = React.createClass({
     *    propTypes: {
     *      // An optional string or URI prop named "href".
     *      href: function(props, propName, componentName) {
     *        var propValue = props[propName];
     *        if (propValue != null && typeof propValue !== 'string' &&
     *            !(propValue instanceof URI)) {
     *          return new Error(
     *            'Expected a string or an URI for ' + propName + ' in ' +
     *            componentName
     *          );
     *        }
     *      }
     *    },
     *    render: function() {...}
     *  });
     *
     * @internal
     */

    var ANONYMOUS = '<<anonymous>>';

    // Important!
    // Keep this list in sync with production version in `./factoryWithThrowingShims.js`.
    var ReactPropTypes = {
      array: createPrimitiveTypeChecker('array'),
      bool: createPrimitiveTypeChecker('boolean'),
      func: createPrimitiveTypeChecker('function'),
      number: createPrimitiveTypeChecker('number'),
      object: createPrimitiveTypeChecker('object'),
      string: createPrimitiveTypeChecker('string'),
      symbol: createPrimitiveTypeChecker('symbol'),

      any: createAnyTypeChecker(),
      arrayOf: createArrayOfTypeChecker,
      element: createElementTypeChecker(),
      elementType: createElementTypeTypeChecker(),
      instanceOf: createInstanceTypeChecker,
      node: createNodeChecker(),
      objectOf: createObjectOfTypeChecker,
      oneOf: createEnumTypeChecker,
      oneOfType: createUnionTypeChecker,
      shape: createShapeTypeChecker,
      exact: createStrictShapeTypeChecker,
    };

    /**
     * inlined Object.is polyfill to avoid requiring consumers ship their own
     * https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is
     */
    /*eslint-disable no-self-compare*/
    function is(x, y) {
      // SameValue algorithm
      if (x === y) {
        // Steps 1-5, 7-10
        // Steps 6.b-6.e: +0 != -0
        return x !== 0 || 1 / x === 1 / y;
      } else {
        // Step 6.a: NaN == NaN
        return x !== x && y !== y;
      }
    }
    /*eslint-enable no-self-compare*/

    /**
     * We use an Error-like object for backward compatibility as people may call
     * PropTypes directly and inspect their output. However, we don't use real
     * Errors anymore. We don't inspect their stack anyway, and creating them
     * is prohibitively expensive if they are created too often, such as what
     * happens in oneOfType() for any type before the one that matched.
     */
    function PropTypeError(message) {
      this.message = message;
      this.stack = '';
    }
    // Make `instanceof Error` still work for returned errors.
    PropTypeError.prototype = Error.prototype;

    function createChainableTypeChecker(validate) {
      if (process.env.NODE_ENV !== 'production') {
        var manualPropTypeCallCache = {};
        var manualPropTypeWarningCount = 0;
      }
      function checkType(isRequired, props, propName, componentName, location, propFullName, secret) {
        componentName = componentName || ANONYMOUS;
        propFullName = propFullName || propName;

        if (secret !== ReactPropTypesSecret_1) {
          if (throwOnDirectAccess) {
            // New behavior only for users of `prop-types` package
            var err = new Error(
              'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
              'Use `PropTypes.checkPropTypes()` to call them. ' +
              'Read more at http://fb.me/use-check-prop-types'
            );
            err.name = 'Invariant Violation';
            throw err;
          } else if (process.env.NODE_ENV !== 'production' && typeof console !== 'undefined') {
            // Old behavior for people using React.PropTypes
            var cacheKey = componentName + ':' + propName;
            if (
              !manualPropTypeCallCache[cacheKey] &&
              // Avoid spamming the console because they are often not actionable except for lib authors
              manualPropTypeWarningCount < 3
            ) {
              printWarning$1(
                'You are manually calling a React.PropTypes validation ' +
                'function for the `' + propFullName + '` prop on `' + componentName  + '`. This is deprecated ' +
                'and will throw in the standalone `prop-types` package. ' +
                'You may be seeing this warning due to a third-party PropTypes ' +
                'library. See https://fb.me/react-warning-dont-call-proptypes ' + 'for details.'
              );
              manualPropTypeCallCache[cacheKey] = true;
              manualPropTypeWarningCount++;
            }
          }
        }
        if (props[propName] == null) {
          if (isRequired) {
            if (props[propName] === null) {
              return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required ' + ('in `' + componentName + '`, but its value is `null`.'));
            }
            return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required in ' + ('`' + componentName + '`, but its value is `undefined`.'));
          }
          return null;
        } else {
          return validate(props, propName, componentName, location, propFullName);
        }
      }

      var chainedCheckType = checkType.bind(null, false);
      chainedCheckType.isRequired = checkType.bind(null, true);

      return chainedCheckType;
    }

    function createPrimitiveTypeChecker(expectedType) {
      function validate(props, propName, componentName, location, propFullName, secret) {
        var propValue = props[propName];
        var propType = getPropType(propValue);
        if (propType !== expectedType) {
          // `propValue` being instance of, say, date/regexp, pass the 'object'
          // check, but we can offer a more precise error message here rather than
          // 'of type `object`'.
          var preciseType = getPreciseType(propValue);

          return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + preciseType + '` supplied to `' + componentName + '`, expected ') + ('`' + expectedType + '`.'));
        }
        return null;
      }
      return createChainableTypeChecker(validate);
    }

    function createAnyTypeChecker() {
      return createChainableTypeChecker(emptyFunctionThatReturnsNull);
    }

    function createArrayOfTypeChecker(typeChecker) {
      function validate(props, propName, componentName, location, propFullName) {
        if (typeof typeChecker !== 'function') {
          return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside arrayOf.');
        }
        var propValue = props[propName];
        if (!Array.isArray(propValue)) {
          var propType = getPropType(propValue);
          return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an array.'));
        }
        for (var i = 0; i < propValue.length; i++) {
          var error = typeChecker(propValue, i, componentName, location, propFullName + '[' + i + ']', ReactPropTypesSecret_1);
          if (error instanceof Error) {
            return error;
          }
        }
        return null;
      }
      return createChainableTypeChecker(validate);
    }

    function createElementTypeChecker() {
      function validate(props, propName, componentName, location, propFullName) {
        var propValue = props[propName];
        if (!isValidElement(propValue)) {
          var propType = getPropType(propValue);
          return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement.'));
        }
        return null;
      }
      return createChainableTypeChecker(validate);
    }

    function createElementTypeTypeChecker() {
      function validate(props, propName, componentName, location, propFullName) {
        var propValue = props[propName];
        if (!reactIs.isValidElementType(propValue)) {
          var propType = getPropType(propValue);
          return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement type.'));
        }
        return null;
      }
      return createChainableTypeChecker(validate);
    }

    function createInstanceTypeChecker(expectedClass) {
      function validate(props, propName, componentName, location, propFullName) {
        if (!(props[propName] instanceof expectedClass)) {
          var expectedClassName = expectedClass.name || ANONYMOUS;
          var actualClassName = getClassName(props[propName]);
          return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + actualClassName + '` supplied to `' + componentName + '`, expected ') + ('instance of `' + expectedClassName + '`.'));
        }
        return null;
      }
      return createChainableTypeChecker(validate);
    }

    function createEnumTypeChecker(expectedValues) {
      if (!Array.isArray(expectedValues)) {
        if (process.env.NODE_ENV !== 'production') {
          if (arguments.length > 1) {
            printWarning$1(
              'Invalid arguments supplied to oneOf, expected an array, got ' + arguments.length + ' arguments. ' +
              'A common mistake is to write oneOf(x, y, z) instead of oneOf([x, y, z]).'
            );
          } else {
            printWarning$1('Invalid argument supplied to oneOf, expected an array.');
          }
        }
        return emptyFunctionThatReturnsNull;
      }

      function validate(props, propName, componentName, location, propFullName) {
        var propValue = props[propName];
        for (var i = 0; i < expectedValues.length; i++) {
          if (is(propValue, expectedValues[i])) {
            return null;
          }
        }

        var valuesString = JSON.stringify(expectedValues, function replacer(key, value) {
          var type = getPreciseType(value);
          if (type === 'symbol') {
            return String(value);
          }
          return value;
        });
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of value `' + String(propValue) + '` ' + ('supplied to `' + componentName + '`, expected one of ' + valuesString + '.'));
      }
      return createChainableTypeChecker(validate);
    }

    function createObjectOfTypeChecker(typeChecker) {
      function validate(props, propName, componentName, location, propFullName) {
        if (typeof typeChecker !== 'function') {
          return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside objectOf.');
        }
        var propValue = props[propName];
        var propType = getPropType(propValue);
        if (propType !== 'object') {
          return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an object.'));
        }
        for (var key in propValue) {
          if (has$1(propValue, key)) {
            var error = typeChecker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
            if (error instanceof Error) {
              return error;
            }
          }
        }
        return null;
      }
      return createChainableTypeChecker(validate);
    }

    function createUnionTypeChecker(arrayOfTypeCheckers) {
      if (!Array.isArray(arrayOfTypeCheckers)) {
        process.env.NODE_ENV !== 'production' ? printWarning$1('Invalid argument supplied to oneOfType, expected an instance of array.') : void 0;
        return emptyFunctionThatReturnsNull;
      }

      for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
        var checker = arrayOfTypeCheckers[i];
        if (typeof checker !== 'function') {
          printWarning$1(
            'Invalid argument supplied to oneOfType. Expected an array of check functions, but ' +
            'received ' + getPostfixForTypeWarning(checker) + ' at index ' + i + '.'
          );
          return emptyFunctionThatReturnsNull;
        }
      }

      function validate(props, propName, componentName, location, propFullName) {
        for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
          var checker = arrayOfTypeCheckers[i];
          if (checker(props, propName, componentName, location, propFullName, ReactPropTypesSecret_1) == null) {
            return null;
          }
        }

        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`.'));
      }
      return createChainableTypeChecker(validate);
    }

    function createNodeChecker() {
      function validate(props, propName, componentName, location, propFullName) {
        if (!isNode(props[propName])) {
          return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`, expected a ReactNode.'));
        }
        return null;
      }
      return createChainableTypeChecker(validate);
    }

    function createShapeTypeChecker(shapeTypes) {
      function validate(props, propName, componentName, location, propFullName) {
        var propValue = props[propName];
        var propType = getPropType(propValue);
        if (propType !== 'object') {
          return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
        }
        for (var key in shapeTypes) {
          var checker = shapeTypes[key];
          if (!checker) {
            continue;
          }
          var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
          if (error) {
            return error;
          }
        }
        return null;
      }
      return createChainableTypeChecker(validate);
    }

    function createStrictShapeTypeChecker(shapeTypes) {
      function validate(props, propName, componentName, location, propFullName) {
        var propValue = props[propName];
        var propType = getPropType(propValue);
        if (propType !== 'object') {
          return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
        }
        // We need to check all keys in case some are required but missing from
        // props.
        var allKeys = objectAssign({}, props[propName], shapeTypes);
        for (var key in allKeys) {
          var checker = shapeTypes[key];
          if (!checker) {
            return new PropTypeError(
              'Invalid ' + location + ' `' + propFullName + '` key `' + key + '` supplied to `' + componentName + '`.' +
              '\nBad object: ' + JSON.stringify(props[propName], null, '  ') +
              '\nValid keys: ' +  JSON.stringify(Object.keys(shapeTypes), null, '  ')
            );
          }
          var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
          if (error) {
            return error;
          }
        }
        return null;
      }

      return createChainableTypeChecker(validate);
    }

    function isNode(propValue) {
      switch (typeof propValue) {
        case 'number':
        case 'string':
        case 'undefined':
          return true;
        case 'boolean':
          return !propValue;
        case 'object':
          if (Array.isArray(propValue)) {
            return propValue.every(isNode);
          }
          if (propValue === null || isValidElement(propValue)) {
            return true;
          }

          var iteratorFn = getIteratorFn(propValue);
          if (iteratorFn) {
            var iterator = iteratorFn.call(propValue);
            var step;
            if (iteratorFn !== propValue.entries) {
              while (!(step = iterator.next()).done) {
                if (!isNode(step.value)) {
                  return false;
                }
              }
            } else {
              // Iterator will provide entry [k,v] tuples rather than values.
              while (!(step = iterator.next()).done) {
                var entry = step.value;
                if (entry) {
                  if (!isNode(entry[1])) {
                    return false;
                  }
                }
              }
            }
          } else {
            return false;
          }

          return true;
        default:
          return false;
      }
    }

    function isSymbol(propType, propValue) {
      // Native Symbol.
      if (propType === 'symbol') {
        return true;
      }

      // falsy value can't be a Symbol
      if (!propValue) {
        return false;
      }

      // 19.4.3.5 Symbol.prototype[@@toStringTag] === 'Symbol'
      if (propValue['@@toStringTag'] === 'Symbol') {
        return true;
      }

      // Fallback for non-spec compliant Symbols which are polyfilled.
      if (typeof Symbol === 'function' && propValue instanceof Symbol) {
        return true;
      }

      return false;
    }

    // Equivalent of `typeof` but with special handling for array and regexp.
    function getPropType(propValue) {
      var propType = typeof propValue;
      if (Array.isArray(propValue)) {
        return 'array';
      }
      if (propValue instanceof RegExp) {
        // Old webkits (at least until Android 4.0) return 'function' rather than
        // 'object' for typeof a RegExp. We'll normalize this here so that /bla/
        // passes PropTypes.object.
        return 'object';
      }
      if (isSymbol(propType, propValue)) {
        return 'symbol';
      }
      return propType;
    }

    // This handles more types than `getPropType`. Only used for error messages.
    // See `createPrimitiveTypeChecker`.
    function getPreciseType(propValue) {
      if (typeof propValue === 'undefined' || propValue === null) {
        return '' + propValue;
      }
      var propType = getPropType(propValue);
      if (propType === 'object') {
        if (propValue instanceof Date) {
          return 'date';
        } else if (propValue instanceof RegExp) {
          return 'regexp';
        }
      }
      return propType;
    }

    // Returns a string that is postfixed to a warning about an invalid type.
    // For example, "undefined" or "of type array"
    function getPostfixForTypeWarning(value) {
      var type = getPreciseType(value);
      switch (type) {
        case 'array':
        case 'object':
          return 'an ' + type;
        case 'boolean':
        case 'date':
        case 'regexp':
          return 'a ' + type;
        default:
          return type;
      }
    }

    // Returns class name of the object, if any.
    function getClassName(propValue) {
      if (!propValue.constructor || !propValue.constructor.name) {
        return ANONYMOUS;
      }
      return propValue.constructor.name;
    }

    ReactPropTypes.checkPropTypes = checkPropTypes_1;
    ReactPropTypes.resetWarningCache = checkPropTypes_1.resetWarningCache;
    ReactPropTypes.PropTypes = ReactPropTypes;

    return ReactPropTypes;
  };

  function emptyFunction() {}
  function emptyFunctionWithReset() {}
  emptyFunctionWithReset.resetWarningCache = emptyFunction;

  var factoryWithThrowingShims = function() {
    function shim(props, propName, componentName, location, propFullName, secret) {
      if (secret === ReactPropTypesSecret_1) {
        // It is still safe when called from React.
        return;
      }
      var err = new Error(
        'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
        'Use PropTypes.checkPropTypes() to call them. ' +
        'Read more at http://fb.me/use-check-prop-types'
      );
      err.name = 'Invariant Violation';
      throw err;
    }  shim.isRequired = shim;
    function getShim() {
      return shim;
    }  // Important!
    // Keep this list in sync with production version in `./factoryWithTypeCheckers.js`.
    var ReactPropTypes = {
      array: shim,
      bool: shim,
      func: shim,
      number: shim,
      object: shim,
      string: shim,
      symbol: shim,

      any: shim,
      arrayOf: getShim,
      element: shim,
      elementType: shim,
      instanceOf: getShim,
      node: shim,
      objectOf: getShim,
      oneOf: getShim,
      oneOfType: getShim,
      shape: getShim,
      exact: getShim,

      checkPropTypes: emptyFunctionWithReset,
      resetWarningCache: emptyFunction
    };

    ReactPropTypes.PropTypes = ReactPropTypes;

    return ReactPropTypes;
  };

  var propTypes = createCommonjsModule(function (module) {
  /**
   * Copyright (c) 2013-present, Facebook, Inc.
   *
   * This source code is licensed under the MIT license found in the
   * LICENSE file in the root directory of this source tree.
   */

  if (process.env.NODE_ENV !== 'production') {
    var ReactIs = reactIs;

    // By explicitly using `prop-types` you are opting into new development behavior.
    // http://fb.me/prop-types-in-prod
    var throwOnDirectAccess = true;
    module.exports = factoryWithTypeCheckers(ReactIs.isElement, throwOnDirectAccess);
  } else {
    // By explicitly using `prop-types` you are opting into new production behavior.
    // http://fb.me/prop-types-in-prod
    module.exports = factoryWithThrowingShims();
  }
  });

  // ==============================
  // NO OP
  // ==============================
  var noop = function noop() {};
  // Class Name Prefixer
  // ==============================

  /**
   String representation of component state for styling with class names.

   Expects an array of strings OR a string/object pair:
   - className(['comp', 'comp-arg', 'comp-arg-2'])
     @returns 'react-select__comp react-select__comp-arg react-select__comp-arg-2'
   - className('comp', { some: true, state: false })
     @returns 'react-select__comp react-select__comp--some'
  */

  function applyPrefixToName(prefix, name) {
    if (!name) {
      return prefix;
    } else if (name[0] === '-') {
      return prefix + name;
    } else {
      return prefix + '__' + name;
    }
  }

  function classNames(prefix, state, className) {
    var arr = [className];

    if (state && prefix) {
      for (var key in state) {
        if (state.hasOwnProperty(key) && state[key]) {
          arr.push("" + applyPrefixToName(prefix, key));
        }
      }
    }

    return arr.filter(function (i) {
      return i;
    }).map(function (i) {
      return String(i).trim();
    }).join(' ');
  } // ==============================
  // Clean Value
  // ==============================

  var cleanValue = function cleanValue(value) {
    if (Array.isArray(value)) return value.filter(Boolean);
    if (typeof value === 'object' && value !== null) return [value];
    return [];
  }; // ==============================
  // Scroll Helpers
  // ==============================

  function isDocumentElement(el) {
    return [document.documentElement, document.body, window].indexOf(el) > -1;
  } // Normalized Scroll Top
  // ------------------------------

  function getScrollTop(el) {
    if (isDocumentElement(el)) {
      return window.pageYOffset;
    }

    return el.scrollTop;
  }
  function scrollTo(el, top) {
    // with a scroll distance, we perform scroll on the element
    if (isDocumentElement(el)) {
      window.scrollTo(0, top);
      return;
    }

    el.scrollTop = top;
  } // Get Scroll Parent
  // ------------------------------

  function getScrollParent(element) {
    var style = getComputedStyle(element);
    var excludeStaticParent = style.position === 'absolute';
    var overflowRx = /(auto|scroll)/;
    var docEl = document.documentElement; // suck it, flow...

    if (style.position === 'fixed') return docEl;

    for (var parent = element; parent = parent.parentElement;) {
      style = getComputedStyle(parent);

      if (excludeStaticParent && style.position === 'static') {
        continue;
      }

      if (overflowRx.test(style.overflow + style.overflowY + style.overflowX)) {
        return parent;
      }
    }

    return docEl;
  } // Animated Scroll To
  // ------------------------------

  /**
    @param t: time (elapsed)
    @param b: initial value
    @param c: amount of change
    @param d: duration
  */

  function easeOutCubic(t, b, c, d) {
    return c * ((t = t / d - 1) * t * t + 1) + b;
  }

  function animatedScrollTo(element, to, duration, callback) {
    if (duration === void 0) {
      duration = 200;
    }

    if (callback === void 0) {
      callback = noop;
    }

    var start = getScrollTop(element);
    var change = to - start;
    var increment = 10;
    var currentTime = 0;

    function animateScroll() {
      currentTime += increment;
      var val = easeOutCubic(currentTime, start, change, duration);
      scrollTo(element, val);

      if (currentTime < duration) {
        window.requestAnimationFrame(animateScroll);
      } else {
        callback(element);
      }
    }

    animateScroll();
  } // Scroll Into View
  // ------------------------------

  function scrollIntoView(menuEl, focusedEl) {
    var menuRect = menuEl.getBoundingClientRect();
    var focusedRect = focusedEl.getBoundingClientRect();
    var overScroll = focusedEl.offsetHeight / 3;

    if (focusedRect.bottom + overScroll > menuRect.bottom) {
      scrollTo(menuEl, Math.min(focusedEl.offsetTop + focusedEl.clientHeight - menuEl.offsetHeight + overScroll, menuEl.scrollHeight));
    } else if (focusedRect.top - overScroll < menuRect.top) {
      scrollTo(menuEl, Math.max(focusedEl.offsetTop - overScroll, 0));
    }
  } // ==============================
  // Get bounding client object
  // ==============================
  // cannot get keys using array notation with DOMRect

  function getBoundingClientObj(element) {
    var rect = element.getBoundingClientRect();
    return {
      bottom: rect.bottom,
      height: rect.height,
      left: rect.left,
      right: rect.right,
      top: rect.top,
      width: rect.width
    };
  }
  // Touch Capability Detector
  // ==============================

  function isTouchCapable() {
    try {
      document.createEvent('TouchEvent');
      return true;
    } catch (e) {
      return false;
    }
  } // ==============================
  // Mobile Device Detector
  // ==============================

  function isMobileDevice() {
    try {
      return /Android|webOS|iPhone|iPad|iPod|BlackBerry|IEMobile|Opera Mini/i.test(navigator.userAgent);
    } catch (e) {
      return false;
    }
  }

  /* eslint-disable */
  // Inspired by https://github.com/garycourt/murmurhash-js
  // Ported from https://github.com/aappleby/smhasher/blob/61a0530f28277f2e850bfc39600ce61d02b518de/src/MurmurHash2.cpp#L37-L86
  function murmur2(str) {
    // 'm' and 'r' are mixing constants generated offline.
    // They're not really 'magic', they just happen to work well.
    // const m = 0x5bd1e995;
    // const r = 24;
    // Initialize the hash
    var h = 0; // Mix 4 bytes at a time into the hash

    var k,
        i = 0,
        len = str.length;

    for (; len >= 4; ++i, len -= 4) {
      k = str.charCodeAt(i) & 0xff | (str.charCodeAt(++i) & 0xff) << 8 | (str.charCodeAt(++i) & 0xff) << 16 | (str.charCodeAt(++i) & 0xff) << 24;
      k =
      /* Math.imul(k, m): */
      (k & 0xffff) * 0x5bd1e995 + ((k >>> 16) * 0xe995 << 16);
      k ^=
      /* k >>> r: */
      k >>> 24;
      h =
      /* Math.imul(k, m): */
      (k & 0xffff) * 0x5bd1e995 + ((k >>> 16) * 0xe995 << 16) ^
      /* Math.imul(h, m): */
      (h & 0xffff) * 0x5bd1e995 + ((h >>> 16) * 0xe995 << 16);
    } // Handle the last few bytes of the input array


    switch (len) {
      case 3:
        h ^= (str.charCodeAt(i + 2) & 0xff) << 16;

      case 2:
        h ^= (str.charCodeAt(i + 1) & 0xff) << 8;

      case 1:
        h ^= str.charCodeAt(i) & 0xff;
        h =
        /* Math.imul(h, m): */
        (h & 0xffff) * 0x5bd1e995 + ((h >>> 16) * 0xe995 << 16);
    } // Do a few final mixes of the hash to ensure the last few
    // bytes are well-incorporated.


    h ^= h >>> 13;
    h =
    /* Math.imul(h, m): */
    (h & 0xffff) * 0x5bd1e995 + ((h >>> 16) * 0xe995 << 16);
    return ((h ^ h >>> 15) >>> 0).toString(36);
  }

  var unitlessKeys = {
    animationIterationCount: 1,
    borderImageOutset: 1,
    borderImageSlice: 1,
    borderImageWidth: 1,
    boxFlex: 1,
    boxFlexGroup: 1,
    boxOrdinalGroup: 1,
    columnCount: 1,
    columns: 1,
    flex: 1,
    flexGrow: 1,
    flexPositive: 1,
    flexShrink: 1,
    flexNegative: 1,
    flexOrder: 1,
    gridRow: 1,
    gridRowEnd: 1,
    gridRowSpan: 1,
    gridRowStart: 1,
    gridColumn: 1,
    gridColumnEnd: 1,
    gridColumnSpan: 1,
    gridColumnStart: 1,
    msGridRow: 1,
    msGridRowSpan: 1,
    msGridColumn: 1,
    msGridColumnSpan: 1,
    fontWeight: 1,
    lineHeight: 1,
    opacity: 1,
    order: 1,
    orphans: 1,
    tabSize: 1,
    widows: 1,
    zIndex: 1,
    zoom: 1,
    WebkitLineClamp: 1,
    // SVG-related properties
    fillOpacity: 1,
    floodOpacity: 1,
    stopOpacity: 1,
    strokeDasharray: 1,
    strokeDashoffset: 1,
    strokeMiterlimit: 1,
    strokeOpacity: 1,
    strokeWidth: 1
  };

  function memoize(fn) {
    var cache = {};
    return function (arg) {
      if (cache[arg] === undefined) cache[arg] = fn(arg);
      return cache[arg];
    };
  }

  var ILLEGAL_ESCAPE_SEQUENCE_ERROR = "You have illegal escape sequence in your template literal, most likely inside content's property value.\nBecause you write your CSS inside a JavaScript string you actually have to do double escaping, so for example \"content: '\\00d7';\" should become \"content: '\\\\00d7';\".\nYou can read more about this here:\nhttps://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Template_literals#ES2018_revision_of_illegal_escape_sequences";
  var UNDEFINED_AS_OBJECT_KEY_ERROR = "You have passed in falsy value as style object's key (can happen when in example you pass unexported component as computed key).";
  var hyphenateRegex = /[A-Z]|^ms/g;
  var animationRegex = /_EMO_([^_]+?)_([^]*?)_EMO_/g;

  var isCustomProperty = function isCustomProperty(property) {
    return property.charCodeAt(1) === 45;
  };

  var isProcessableValue = function isProcessableValue(value) {
    return value != null && typeof value !== 'boolean';
  };

  var processStyleName = memoize(function (styleName) {
    return isCustomProperty(styleName) ? styleName : styleName.replace(hyphenateRegex, '-$&').toLowerCase();
  });

  var processStyleValue = function processStyleValue(key, value) {
    switch (key) {
      case 'animation':
      case 'animationName':
        {
          if (typeof value === 'string') {
            return value.replace(animationRegex, function (match, p1, p2) {
              cursor = {
                name: p1,
                styles: p2,
                next: cursor
              };
              return p1;
            });
          }
        }
    }

    if (unitlessKeys[key] !== 1 && !isCustomProperty(key) && typeof value === 'number' && value !== 0) {
      return value + 'px';
    }

    return value;
  };

  if (process.env.NODE_ENV !== 'production') {
    var contentValuePattern = /(attr|calc|counters?|url)\(/;
    var contentValues = ['normal', 'none', 'counter', 'open-quote', 'close-quote', 'no-open-quote', 'no-close-quote', 'initial', 'inherit', 'unset'];
    var oldProcessStyleValue = processStyleValue;
    var msPattern = /^-ms-/;
    var hyphenPattern = /-(.)/g;
    var hyphenatedCache = {};

    processStyleValue = function processStyleValue(key, value) {
      if (key === 'content') {
        if (typeof value !== 'string' || contentValues.indexOf(value) === -1 && !contentValuePattern.test(value) && (value.charAt(0) !== value.charAt(value.length - 1) || value.charAt(0) !== '"' && value.charAt(0) !== "'")) {
          console.error("You seem to be using a value for 'content' without quotes, try replacing it with `content: '\"" + value + "\"'`");
        }
      }

      var processed = oldProcessStyleValue(key, value);

      if (processed !== '' && !isCustomProperty(key) && key.indexOf('-') !== -1 && hyphenatedCache[key] === undefined) {
        hyphenatedCache[key] = true;
        console.error("Using kebab-case for css properties in objects is not supported. Did you mean " + key.replace(msPattern, 'ms-').replace(hyphenPattern, function (str, _char) {
          return _char.toUpperCase();
        }) + "?");
      }

      return processed;
    };
  }

  var shouldWarnAboutInterpolatingClassNameFromCss = true;

  function handleInterpolation(mergedProps, registered, interpolation, couldBeSelectorInterpolation) {
    if (interpolation == null) {
      return '';
    }

    if (interpolation.__emotion_styles !== undefined) {
      if (process.env.NODE_ENV !== 'production' && interpolation.toString() === 'NO_COMPONENT_SELECTOR') {
        throw new Error('Component selectors can only be used in conjunction with babel-plugin-emotion.');
      }

      return interpolation;
    }

    switch (typeof interpolation) {
      case 'boolean':
        {
          return '';
        }

      case 'object':
        {
          if (interpolation.anim === 1) {
            cursor = {
              name: interpolation.name,
              styles: interpolation.styles,
              next: cursor
            };
            return interpolation.name;
          }

          if (interpolation.styles !== undefined) {
            var next = interpolation.next;

            if (next !== undefined) {
              // not the most efficient thing ever but this is a pretty rare case
              // and there will be very few iterations of this generally
              while (next !== undefined) {
                cursor = {
                  name: next.name,
                  styles: next.styles,
                  next: cursor
                };
                next = next.next;
              }
            }

            var styles = interpolation.styles + ";";

            if (process.env.NODE_ENV !== 'production' && interpolation.map !== undefined) {
              styles += interpolation.map;
            }

            return styles;
          }

          return createStringFromObject(mergedProps, registered, interpolation);
        }

      case 'function':
        {
          if (mergedProps !== undefined) {
            var previousCursor = cursor;
            var result = interpolation(mergedProps);
            cursor = previousCursor;
            return handleInterpolation(mergedProps, registered, result, couldBeSelectorInterpolation);
          } else if (process.env.NODE_ENV !== 'production') {
            console.error('Functions that are interpolated in css calls will be stringified.\n' + 'If you want to have a css call based on props, create a function that returns a css call like this\n' + 'let dynamicStyle = (props) => css`color: ${props.color}`\n' + 'It can be called directly with props or interpolated in a styled call like this\n' + "let SomeComponent = styled('div')`${dynamicStyle}`");
          }

          break;
        }

      case 'string':
        if (process.env.NODE_ENV !== 'production') {
          var matched = [];
          var replaced = interpolation.replace(animationRegex, function (match, p1, p2) {
            var fakeVarName = "animation" + matched.length;
            matched.push("const " + fakeVarName + " = keyframes`" + p2.replace(/^@keyframes animation-\w+/, '') + "`");
            return "${" + fakeVarName + "}";
          });

          if (matched.length) {
            console.error('`keyframes` output got interpolated into plain string, please wrap it with `css`.\n\n' + 'Instead of doing this:\n\n' + [].concat(matched, ["`" + replaced + "`"]).join('\n') + '\n\nYou should wrap it with `css` like this:\n\n' + ("css`" + replaced + "`"));
          }
        }

        break;
    } // finalize string values (regular strings and functions interpolated into css calls)


    if (registered == null) {
      return interpolation;
    }

    var cached = registered[interpolation];

    if (process.env.NODE_ENV !== 'production' && couldBeSelectorInterpolation && shouldWarnAboutInterpolatingClassNameFromCss && cached !== undefined) {
      console.error('Interpolating a className from css`` is not recommended and will cause problems with composition.\n' + 'Interpolating a className from css`` will be completely unsupported in a future major version of Emotion');
      shouldWarnAboutInterpolatingClassNameFromCss = false;
    }

    return cached !== undefined && !couldBeSelectorInterpolation ? cached : interpolation;
  }

  function createStringFromObject(mergedProps, registered, obj) {
    var string = '';

    if (Array.isArray(obj)) {
      for (var i = 0; i < obj.length; i++) {
        string += handleInterpolation(mergedProps, registered, obj[i], false);
      }
    } else {
      for (var _key in obj) {
        var value = obj[_key];

        if (typeof value !== 'object') {
          if (registered != null && registered[value] !== undefined) {
            string += _key + "{" + registered[value] + "}";
          } else if (isProcessableValue(value)) {
            string += processStyleName(_key) + ":" + processStyleValue(_key, value) + ";";
          }
        } else {
          if (_key === 'NO_COMPONENT_SELECTOR' && process.env.NODE_ENV !== 'production') {
            throw new Error('Component selectors can only be used in conjunction with babel-plugin-emotion.');
          }

          if (Array.isArray(value) && typeof value[0] === 'string' && (registered == null || registered[value[0]] === undefined)) {
            for (var _i = 0; _i < value.length; _i++) {
              if (isProcessableValue(value[_i])) {
                string += processStyleName(_key) + ":" + processStyleValue(_key, value[_i]) + ";";
              }
            }
          } else {
            var interpolated = handleInterpolation(mergedProps, registered, value, false);

            switch (_key) {
              case 'animation':
              case 'animationName':
                {
                  string += processStyleName(_key) + ":" + interpolated + ";";
                  break;
                }

              default:
                {
                  if (process.env.NODE_ENV !== 'production' && _key === 'undefined') {
                    console.error(UNDEFINED_AS_OBJECT_KEY_ERROR);
                  }

                  string += _key + "{" + interpolated + "}";
                }
            }
          }
        }
      }
    }

    return string;
  }

  var labelPattern = /label:\s*([^\s;\n{]+)\s*;/g;
  var sourceMapPattern;

  if (process.env.NODE_ENV !== 'production') {
    sourceMapPattern = /\/\*#\ssourceMappingURL=data:application\/json;\S+\s+\*\//;
  } // this is the cursor for keyframes
  // keyframes are stored on the SerializedStyles object as a linked list


  var cursor;
  var serializeStyles = function serializeStyles(args, registered, mergedProps) {
    if (args.length === 1 && typeof args[0] === 'object' && args[0] !== null && args[0].styles !== undefined) {
      return args[0];
    }

    var stringMode = true;
    var styles = '';
    cursor = undefined;
    var strings = args[0];

    if (strings == null || strings.raw === undefined) {
      stringMode = false;
      styles += handleInterpolation(mergedProps, registered, strings, false);
    } else {
      if (process.env.NODE_ENV !== 'production' && strings[0] === undefined) {
        console.error(ILLEGAL_ESCAPE_SEQUENCE_ERROR);
      }

      styles += strings[0];
    } // we start at 1 since we've already handled the first arg


    for (var i = 1; i < args.length; i++) {
      styles += handleInterpolation(mergedProps, registered, args[i], styles.charCodeAt(styles.length - 1) === 46);

      if (stringMode) {
        if (process.env.NODE_ENV !== 'production' && strings[i] === undefined) {
          console.error(ILLEGAL_ESCAPE_SEQUENCE_ERROR);
        }

        styles += strings[i];
      }
    }

    var sourceMap;

    if (process.env.NODE_ENV !== 'production') {
      styles = styles.replace(sourceMapPattern, function (match) {
        sourceMap = match;
        return '';
      });
    } // using a global regex with .exec is stateful so lastIndex has to be reset each time


    labelPattern.lastIndex = 0;
    var identifierName = '';
    var match; // https://esbench.com/bench/5b809c2cf2949800a0f61fb5

    while ((match = labelPattern.exec(styles)) !== null) {
      identifierName += '-' + // $FlowFixMe we know it's not null
      match[1];
    }

    var name = murmur2(styles) + identifierName;

    if (process.env.NODE_ENV !== 'production') {
      // $FlowFixMe SerializedStyles type doesn't have toString property (and we don't want to add it)
      return {
        name: name,
        styles: styles,
        map: sourceMap,
        next: cursor,
        toString: function toString() {
          return "You have tried to stringify object returned from `css` function. It isn't supposed to be used directly (e.g. as value of the `className` prop), but rather handed to emotion so it can handle it (e.g. as value of `css` prop).";
        }
      };
    }

    return {
      name: name,
      styles: styles,
      next: cursor
    };
  };

  function css() {
    for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
      args[_key] = arguments[_key];
    }

    return serializeStyles(args);
  }

  var AutosizeInput_1 = createCommonjsModule(function (module, exports) {

  Object.defineProperty(exports, "__esModule", {
  	value: true
  });

  var _extends = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; };

  var _createClass = function () { function defineProperties(target, props) { for (var i = 0; i < props.length; i++) { var descriptor = props[i]; descriptor.enumerable = descriptor.enumerable || false; descriptor.configurable = true; if ("value" in descriptor) descriptor.writable = true; Object.defineProperty(target, descriptor.key, descriptor); } } return function (Constructor, protoProps, staticProps) { if (protoProps) defineProperties(Constructor.prototype, protoProps); if (staticProps) defineProperties(Constructor, staticProps); return Constructor; }; }();



  var _react2 = _interopRequireDefault(React__default);



  var _propTypes2 = _interopRequireDefault(propTypes);

  function _interopRequireDefault(obj) { return obj && obj.__esModule ? obj : { default: obj }; }

  function _objectWithoutProperties(obj, keys) { var target = {}; for (var i in obj) { if (keys.indexOf(i) >= 0) continue; if (!Object.prototype.hasOwnProperty.call(obj, i)) continue; target[i] = obj[i]; } return target; }

  function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

  function _possibleConstructorReturn(self, call) { if (!self) { throw new ReferenceError("this hasn't been initialised - super() hasn't been called"); } return call && (typeof call === "object" || typeof call === "function") ? call : self; }

  function _inherits(subClass, superClass) { if (typeof superClass !== "function" && superClass !== null) { throw new TypeError("Super expression must either be null or a function, not " + typeof superClass); } subClass.prototype = Object.create(superClass && superClass.prototype, { constructor: { value: subClass, enumerable: false, writable: true, configurable: true } }); if (superClass) Object.setPrototypeOf ? Object.setPrototypeOf(subClass, superClass) : subClass.__proto__ = superClass; }

  var sizerStyle = {
  	position: 'absolute',
  	top: 0,
  	left: 0,
  	visibility: 'hidden',
  	height: 0,
  	overflow: 'scroll',
  	whiteSpace: 'pre'
  };

  var INPUT_PROPS_BLACKLIST = ['extraWidth', 'injectStyles', 'inputClassName', 'inputRef', 'inputStyle', 'minWidth', 'onAutosize', 'placeholderIsMinWidth'];

  var cleanInputProps = function cleanInputProps(inputProps) {
  	INPUT_PROPS_BLACKLIST.forEach(function (field) {
  		return delete inputProps[field];
  	});
  	return inputProps;
  };

  var copyStyles = function copyStyles(styles, node) {
  	node.style.fontSize = styles.fontSize;
  	node.style.fontFamily = styles.fontFamily;
  	node.style.fontWeight = styles.fontWeight;
  	node.style.fontStyle = styles.fontStyle;
  	node.style.letterSpacing = styles.letterSpacing;
  	node.style.textTransform = styles.textTransform;
  };

  var isIE = typeof window !== 'undefined' && window.navigator ? /MSIE |Trident\/|Edge\//.test(window.navigator.userAgent) : false;

  var generateId = function generateId() {
  	// we only need an auto-generated ID for stylesheet injection, which is only
  	// used for IE. so if the browser is not IE, this should return undefined.
  	return isIE ? '_' + Math.random().toString(36).substr(2, 12) : undefined;
  };

  var AutosizeInput = function (_Component) {
  	_inherits(AutosizeInput, _Component);

  	function AutosizeInput(props) {
  		_classCallCheck(this, AutosizeInput);

  		var _this = _possibleConstructorReturn(this, (AutosizeInput.__proto__ || Object.getPrototypeOf(AutosizeInput)).call(this, props));

  		_this.inputRef = function (el) {
  			_this.input = el;
  			if (typeof _this.props.inputRef === 'function') {
  				_this.props.inputRef(el);
  			}
  		};

  		_this.placeHolderSizerRef = function (el) {
  			_this.placeHolderSizer = el;
  		};

  		_this.sizerRef = function (el) {
  			_this.sizer = el;
  		};

  		_this.state = {
  			inputWidth: props.minWidth,
  			inputId: props.id || generateId()
  		};
  		return _this;
  	}

  	_createClass(AutosizeInput, [{
  		key: 'componentDidMount',
  		value: function componentDidMount() {
  			this.mounted = true;
  			this.copyInputStyles();
  			this.updateInputWidth();
  		}
  	}, {
  		key: 'UNSAFE_componentWillReceiveProps',
  		value: function UNSAFE_componentWillReceiveProps(nextProps) {
  			var id = nextProps.id;

  			if (id !== this.props.id) {
  				this.setState({ inputId: id || generateId() });
  			}
  		}
  	}, {
  		key: 'componentDidUpdate',
  		value: function componentDidUpdate(prevProps, prevState) {
  			if (prevState.inputWidth !== this.state.inputWidth) {
  				if (typeof this.props.onAutosize === 'function') {
  					this.props.onAutosize(this.state.inputWidth);
  				}
  			}
  			this.updateInputWidth();
  		}
  	}, {
  		key: 'componentWillUnmount',
  		value: function componentWillUnmount() {
  			this.mounted = false;
  		}
  	}, {
  		key: 'copyInputStyles',
  		value: function copyInputStyles() {
  			if (!this.mounted || !window.getComputedStyle) {
  				return;
  			}
  			var inputStyles = this.input && window.getComputedStyle(this.input);
  			if (!inputStyles) {
  				return;
  			}
  			copyStyles(inputStyles, this.sizer);
  			if (this.placeHolderSizer) {
  				copyStyles(inputStyles, this.placeHolderSizer);
  			}
  		}
  	}, {
  		key: 'updateInputWidth',
  		value: function updateInputWidth() {
  			if (!this.mounted || !this.sizer || typeof this.sizer.scrollWidth === 'undefined') {
  				return;
  			}
  			var newInputWidth = void 0;
  			if (this.props.placeholder && (!this.props.value || this.props.value && this.props.placeholderIsMinWidth)) {
  				newInputWidth = Math.max(this.sizer.scrollWidth, this.placeHolderSizer.scrollWidth) + 2;
  			} else {
  				newInputWidth = this.sizer.scrollWidth + 2;
  			}
  			// add extraWidth to the detected width. for number types, this defaults to 16 to allow for the stepper UI
  			var extraWidth = this.props.type === 'number' && this.props.extraWidth === undefined ? 16 : parseInt(this.props.extraWidth) || 0;
  			newInputWidth += extraWidth;
  			if (newInputWidth < this.props.minWidth) {
  				newInputWidth = this.props.minWidth;
  			}
  			if (newInputWidth !== this.state.inputWidth) {
  				this.setState({
  					inputWidth: newInputWidth
  				});
  			}
  		}
  	}, {
  		key: 'getInput',
  		value: function getInput() {
  			return this.input;
  		}
  	}, {
  		key: 'focus',
  		value: function focus() {
  			this.input.focus();
  		}
  	}, {
  		key: 'blur',
  		value: function blur() {
  			this.input.blur();
  		}
  	}, {
  		key: 'select',
  		value: function select() {
  			this.input.select();
  		}
  	}, {
  		key: 'renderStyles',
  		value: function renderStyles() {
  			// this method injects styles to hide IE's clear indicator, which messes
  			// with input size detection. the stylesheet is only injected when the
  			// browser is IE, and can also be disabled by the `injectStyles` prop.
  			var injectStyles = this.props.injectStyles;

  			return isIE && injectStyles ? _react2.default.createElement('style', { dangerouslySetInnerHTML: {
  					__html: 'input#' + this.state.inputId + '::-ms-clear {display: none;}'
  				} }) : null;
  		}
  	}, {
  		key: 'render',
  		value: function render() {
  			var sizerValue = [this.props.defaultValue, this.props.value, ''].reduce(function (previousValue, currentValue) {
  				if (previousValue !== null && previousValue !== undefined) {
  					return previousValue;
  				}
  				return currentValue;
  			});

  			var wrapperStyle = _extends({}, this.props.style);
  			if (!wrapperStyle.display) wrapperStyle.display = 'inline-block';

  			var inputStyle = _extends({
  				boxSizing: 'content-box',
  				width: this.state.inputWidth + 'px'
  			}, this.props.inputStyle);

  			var inputProps = _objectWithoutProperties(this.props, []);

  			cleanInputProps(inputProps);
  			inputProps.className = this.props.inputClassName;
  			inputProps.id = this.state.inputId;
  			inputProps.style = inputStyle;

  			return _react2.default.createElement(
  				'div',
  				{ className: this.props.className, style: wrapperStyle },
  				this.renderStyles(),
  				_react2.default.createElement('input', _extends({}, inputProps, { ref: this.inputRef })),
  				_react2.default.createElement(
  					'div',
  					{ ref: this.sizerRef, style: sizerStyle },
  					sizerValue
  				),
  				this.props.placeholder ? _react2.default.createElement(
  					'div',
  					{ ref: this.placeHolderSizerRef, style: sizerStyle },
  					this.props.placeholder
  				) : null
  			);
  		}
  	}]);

  	return AutosizeInput;
  }(React__default.Component);

  AutosizeInput.propTypes = {
  	className: _propTypes2.default.string, // className for the outer element
  	defaultValue: _propTypes2.default.any, // default field value
  	extraWidth: _propTypes2.default.oneOfType([// additional width for input element
  	_propTypes2.default.number, _propTypes2.default.string]),
  	id: _propTypes2.default.string, // id to use for the input, can be set for consistent snapshots
  	injectStyles: _propTypes2.default.bool, // inject the custom stylesheet to hide clear UI, defaults to true
  	inputClassName: _propTypes2.default.string, // className for the input element
  	inputRef: _propTypes2.default.func, // ref callback for the input element
  	inputStyle: _propTypes2.default.object, // css styles for the input element
  	minWidth: _propTypes2.default.oneOfType([// minimum width for input element
  	_propTypes2.default.number, _propTypes2.default.string]),
  	onAutosize: _propTypes2.default.func, // onAutosize handler: function(newWidth) {}
  	onChange: _propTypes2.default.func, // onChange handler: function(event) {}
  	placeholder: _propTypes2.default.string, // placeholder text
  	placeholderIsMinWidth: _propTypes2.default.bool, // don't collapse size to less than the placeholder
  	style: _propTypes2.default.object, // css styles for the outer element
  	value: _propTypes2.default.any // field value
  };
  AutosizeInput.defaultProps = {
  	minWidth: 1,
  	injectStyles: true
  };

  exports.default = AutosizeInput;
  });

  var AutosizeInput = unwrapExports(AutosizeInput_1);

  function _extends$1() { _extends$1 = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; }; return _extends$1.apply(this, arguments); }

  function _inheritsLoose(subClass, superClass) { subClass.prototype = Object.create(superClass.prototype); subClass.prototype.constructor = subClass; subClass.__proto__ = superClass; }
  function getMenuPlacement(_ref) {
    var maxHeight = _ref.maxHeight,
        menuEl = _ref.menuEl,
        minHeight = _ref.minHeight,
        placement = _ref.placement,
        shouldScroll = _ref.shouldScroll,
        isFixedPosition = _ref.isFixedPosition,
        theme = _ref.theme;
    var spacing = theme.spacing;
    var scrollParent = getScrollParent(menuEl);
    var defaultState = {
      placement: 'bottom',
      maxHeight: maxHeight
    }; // something went wrong, return default state

    if (!menuEl || !menuEl.offsetParent) return defaultState; // we can't trust `scrollParent.scrollHeight` --> it may increase when
    // the menu is rendered

    var _scrollParent$getBoun = scrollParent.getBoundingClientRect(),
        scrollHeight = _scrollParent$getBoun.height;

    var _menuEl$getBoundingCl = menuEl.getBoundingClientRect(),
        menuBottom = _menuEl$getBoundingCl.bottom,
        menuHeight = _menuEl$getBoundingCl.height,
        menuTop = _menuEl$getBoundingCl.top;

    var _menuEl$offsetParent$ = menuEl.offsetParent.getBoundingClientRect(),
        containerTop = _menuEl$offsetParent$.top;

    var viewHeight = window.innerHeight;
    var scrollTop = getScrollTop(scrollParent);
    var marginBottom = parseInt(getComputedStyle(menuEl).marginBottom, 10);
    var marginTop = parseInt(getComputedStyle(menuEl).marginTop, 10);
    var viewSpaceAbove = containerTop - marginTop;
    var viewSpaceBelow = viewHeight - menuTop;
    var scrollSpaceAbove = viewSpaceAbove + scrollTop;
    var scrollSpaceBelow = scrollHeight - scrollTop - menuTop;
    var scrollDown = menuBottom - viewHeight + scrollTop + marginBottom;
    var scrollUp = scrollTop + menuTop - marginTop;
    var scrollDuration = 160;

    switch (placement) {
      case 'auto':
      case 'bottom':
        // 1: the menu will fit, do nothing
        if (viewSpaceBelow >= menuHeight) {
          return {
            placement: 'bottom',
            maxHeight: maxHeight
          };
        } // 2: the menu will fit, if scrolled


        if (scrollSpaceBelow >= menuHeight && !isFixedPosition) {
          if (shouldScroll) {
            animatedScrollTo(scrollParent, scrollDown, scrollDuration);
          }

          return {
            placement: 'bottom',
            maxHeight: maxHeight
          };
        } // 3: the menu will fit, if constrained


        if (!isFixedPosition && scrollSpaceBelow >= minHeight || isFixedPosition && viewSpaceBelow >= minHeight) {
          if (shouldScroll) {
            animatedScrollTo(scrollParent, scrollDown, scrollDuration);
          } // we want to provide as much of the menu as possible to the user,
          // so give them whatever is available below rather than the minHeight.


          var constrainedHeight = isFixedPosition ? viewSpaceBelow - marginBottom : scrollSpaceBelow - marginBottom;
          return {
            placement: 'bottom',
            maxHeight: constrainedHeight
          };
        } // 4. Forked beviour when there isn't enough space below
        // AUTO: flip the menu, render above


        if (placement === 'auto' || isFixedPosition) {
          // may need to be constrained after flipping
          var _constrainedHeight = maxHeight;
          var spaceAbove = isFixedPosition ? viewSpaceAbove : scrollSpaceAbove;

          if (spaceAbove >= minHeight) {
            _constrainedHeight = Math.min(spaceAbove - marginBottom - spacing.controlHeight, maxHeight);
          }

          return {
            placement: 'top',
            maxHeight: _constrainedHeight
          };
        } // BOTTOM: allow browser to increase scrollable area and immediately set scroll


        if (placement === 'bottom') {
          scrollTo(scrollParent, scrollDown);
          return {
            placement: 'bottom',
            maxHeight: maxHeight
          };
        }

        break;

      case 'top':
        // 1: the menu will fit, do nothing
        if (viewSpaceAbove >= menuHeight) {
          return {
            placement: 'top',
            maxHeight: maxHeight
          };
        } // 2: the menu will fit, if scrolled


        if (scrollSpaceAbove >= menuHeight && !isFixedPosition) {
          if (shouldScroll) {
            animatedScrollTo(scrollParent, scrollUp, scrollDuration);
          }

          return {
            placement: 'top',
            maxHeight: maxHeight
          };
        } // 3: the menu will fit, if constrained


        if (!isFixedPosition && scrollSpaceAbove >= minHeight || isFixedPosition && viewSpaceAbove >= minHeight) {
          var _constrainedHeight2 = maxHeight; // we want to provide as much of the menu as possible to the user,
          // so give them whatever is available below rather than the minHeight.

          if (!isFixedPosition && scrollSpaceAbove >= minHeight || isFixedPosition && viewSpaceAbove >= minHeight) {
            _constrainedHeight2 = isFixedPosition ? viewSpaceAbove - marginTop : scrollSpaceAbove - marginTop;
          }

          if (shouldScroll) {
            animatedScrollTo(scrollParent, scrollUp, scrollDuration);
          }

          return {
            placement: 'top',
            maxHeight: _constrainedHeight2
          };
        } // 4. not enough space, the browser WILL NOT increase scrollable area when
        // absolutely positioned element rendered above the viewport (only below).
        // Flip the menu, render below


        return {
          placement: 'bottom',
          maxHeight: maxHeight
        };

      default:
        throw new Error("Invalid placement provided \"" + placement + "\".");
    } // fulfil contract with flow: implicit return value of undefined


    return defaultState;
  } // Menu Component
  // ------------------------------

  function alignToControl(placement) {
    var placementToCSSProp = {
      bottom: 'top',
      top: 'bottom'
    };
    return placement ? placementToCSSProp[placement] : 'bottom';
  }

  var coercePlacement = function coercePlacement(p) {
    return p === 'auto' ? 'bottom' : p;
  };

  var menuCSS = function menuCSS(_ref2) {
    var _ref3;

    var placement = _ref2.placement,
        _ref2$theme = _ref2.theme,
        borderRadius = _ref2$theme.borderRadius,
        spacing = _ref2$theme.spacing,
        colors = _ref2$theme.colors;
    return _ref3 = {
      label: 'menu'
    }, _ref3[alignToControl(placement)] = '100%', _ref3.backgroundColor = colors.neutral0, _ref3.borderRadius = borderRadius, _ref3.boxShadow = '0 0 0 1px hsla(0, 0%, 0%, 0.1), 0 4px 11px hsla(0, 0%, 0%, 0.1)', _ref3.marginBottom = spacing.menuGutter, _ref3.marginTop = spacing.menuGutter, _ref3.position = 'absolute', _ref3.width = '100%', _ref3.zIndex = 1, _ref3;
  }; // NOTE: internal only

  var MenuPlacer =
  /*#__PURE__*/
  function (_Component) {
    _inheritsLoose(MenuPlacer, _Component);

    function MenuPlacer() {
      var _this;

      for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
        args[_key] = arguments[_key];
      }

      _this = _Component.call.apply(_Component, [this].concat(args)) || this;
      _this.state = {
        maxHeight: _this.props.maxMenuHeight,
        placement: null
      };

      _this.getPlacement = function (ref) {
        var _this$props = _this.props,
            minMenuHeight = _this$props.minMenuHeight,
            maxMenuHeight = _this$props.maxMenuHeight,
            menuPlacement = _this$props.menuPlacement,
            menuPosition = _this$props.menuPosition,
            menuShouldScrollIntoView = _this$props.menuShouldScrollIntoView,
            theme = _this$props.theme;
        var getPortalPlacement = _this.context.getPortalPlacement;
        if (!ref) return; // DO NOT scroll if position is fixed

        var isFixedPosition = menuPosition === 'fixed';
        var shouldScroll = menuShouldScrollIntoView && !isFixedPosition;
        var state = getMenuPlacement({
          maxHeight: maxMenuHeight,
          menuEl: ref,
          minHeight: minMenuHeight,
          placement: menuPlacement,
          shouldScroll: shouldScroll,
          isFixedPosition: isFixedPosition,
          theme: theme
        });
        if (getPortalPlacement) getPortalPlacement(state);

        _this.setState(state);
      };

      _this.getUpdatedProps = function () {
        var menuPlacement = _this.props.menuPlacement;
        var placement = _this.state.placement || coercePlacement(menuPlacement);
        return _extends$1({}, _this.props, {
          placement: placement,
          maxHeight: _this.state.maxHeight
        });
      };

      return _this;
    }

    var _proto = MenuPlacer.prototype;

    _proto.render = function render() {
      var children = this.props.children;
      return children({
        ref: this.getPlacement,
        placerProps: this.getUpdatedProps()
      });
    };

    return MenuPlacer;
  }(React.Component);
  MenuPlacer.contextTypes = {
    getPortalPlacement: propTypes.func
  };

  var Menu = function Menu(props) {
    var children = props.children,
        className = props.className,
        cx = props.cx,
        getStyles = props.getStyles,
        innerRef = props.innerRef,
        innerProps = props.innerProps;
    return core.jsx("div", _extends$1({
      css: getStyles('menu', props),
      className: cx({
        menu: true
      }, className)
    }, innerProps, {
      ref: innerRef
    }), children);
  };
  // Menu List
  // ==============================

  var menuListCSS = function menuListCSS(_ref4) {
    var maxHeight = _ref4.maxHeight,
        baseUnit = _ref4.theme.spacing.baseUnit;
    return {
      maxHeight: maxHeight,
      overflowY: 'auto',
      paddingBottom: baseUnit,
      paddingTop: baseUnit,
      position: 'relative',
      // required for offset[Height, Top] > keyboard scroll
      WebkitOverflowScrolling: 'touch'
    };
  };
  var MenuList = function MenuList(props) {
    var children = props.children,
        className = props.className,
        cx = props.cx,
        getStyles = props.getStyles,
        isMulti = props.isMulti,
        innerRef = props.innerRef;
    return core.jsx("div", {
      css: getStyles('menuList', props),
      className: cx({
        'menu-list': true,
        'menu-list--is-multi': isMulti
      }, className),
      ref: innerRef
    }, children);
  }; // ==============================
  // Menu Notices
  // ==============================

  var noticeCSS = function noticeCSS(_ref5) {
    var _ref5$theme = _ref5.theme,
        baseUnit = _ref5$theme.spacing.baseUnit,
        colors = _ref5$theme.colors;
    return {
      color: colors.neutral40,
      padding: baseUnit * 2 + "px " + baseUnit * 3 + "px",
      textAlign: 'center'
    };
  };

  var noOptionsMessageCSS = noticeCSS;
  var loadingMessageCSS = noticeCSS;
  var NoOptionsMessage = function NoOptionsMessage(props) {
    var children = props.children,
        className = props.className,
        cx = props.cx,
        getStyles = props.getStyles,
        innerProps = props.innerProps;
    return core.jsx("div", _extends$1({
      css: getStyles('noOptionsMessage', props),
      className: cx({
        'menu-notice': true,
        'menu-notice--no-options': true
      }, className)
    }, innerProps), children);
  };
  NoOptionsMessage.defaultProps = {
    children: 'No options'
  };
  var LoadingMessage = function LoadingMessage(props) {
    var children = props.children,
        className = props.className,
        cx = props.cx,
        getStyles = props.getStyles,
        innerProps = props.innerProps;
    return core.jsx("div", _extends$1({
      css: getStyles('loadingMessage', props),
      className: cx({
        'menu-notice': true,
        'menu-notice--loading': true
      }, className)
    }, innerProps), children);
  };
  LoadingMessage.defaultProps = {
    children: 'Loading...'
  }; // ==============================
  // Menu Portal
  // ==============================

  var menuPortalCSS = function menuPortalCSS(_ref6) {
    var rect = _ref6.rect,
        offset = _ref6.offset,
        position = _ref6.position;
    return {
      left: rect.left,
      position: position,
      top: offset,
      width: rect.width,
      zIndex: 1
    };
  };
  var MenuPortal =
  /*#__PURE__*/
  function (_Component2) {
    _inheritsLoose(MenuPortal, _Component2);

    function MenuPortal() {
      var _this2;

      for (var _len2 = arguments.length, args = new Array(_len2), _key2 = 0; _key2 < _len2; _key2++) {
        args[_key2] = arguments[_key2];
      }

      _this2 = _Component2.call.apply(_Component2, [this].concat(args)) || this;
      _this2.state = {
        placement: null
      };

      _this2.getPortalPlacement = function (_ref7) {
        var placement = _ref7.placement;
        var initialPlacement = coercePlacement(_this2.props.menuPlacement); // avoid re-renders if the placement has not changed

        if (placement !== initialPlacement) {
          _this2.setState({
            placement: placement
          });
        }
      };

      return _this2;
    }

    var _proto2 = MenuPortal.prototype;

    _proto2.getChildContext = function getChildContext() {
      return {
        getPortalPlacement: this.getPortalPlacement
      };
    } // callback for occassions where the menu must "flip"
    ;

    _proto2.render = function render() {
      var _this$props2 = this.props,
          appendTo = _this$props2.appendTo,
          children = _this$props2.children,
          controlElement = _this$props2.controlElement,
          menuPlacement = _this$props2.menuPlacement,
          position = _this$props2.menuPosition,
          getStyles = _this$props2.getStyles;
      var isFixed = position === 'fixed'; // bail early if required elements aren't present

      if (!appendTo && !isFixed || !controlElement) {
        return null;
      }

      var placement = this.state.placement || coercePlacement(menuPlacement);
      var rect = getBoundingClientObj(controlElement);
      var scrollDistance = isFixed ? 0 : window.pageYOffset;
      var offset = rect[placement] + scrollDistance;
      var state = {
        offset: offset,
        position: position,
        rect: rect
      }; // same wrapper element whether fixed or portalled

      var menuWrapper = core.jsx("div", {
        css: getStyles('menuPortal', state)
      }, children);
      return appendTo ? reactDom.createPortal(menuWrapper, appendTo) : menuWrapper;
    };

    return MenuPortal;
  }(React.Component);
  MenuPortal.childContextTypes = {
    getPortalPlacement: propTypes.func
  };

  var isArray = Array.isArray;
  var keyList = Object.keys;
  var hasProp = Object.prototype.hasOwnProperty;

  function equal(a, b) {
    // fast-deep-equal index.js 2.0.1
    if (a === b) return true;

    if (a && b && typeof a == 'object' && typeof b == 'object') {
      var arrA = isArray(a),
          arrB = isArray(b),
          i,
          length,
          key;

      if (arrA && arrB) {
        length = a.length;
        if (length != b.length) return false;

        for (i = length; i-- !== 0;) {
          if (!equal(a[i], b[i])) return false;
        }

        return true;
      }

      if (arrA != arrB) return false;
      var dateA = a instanceof Date,
          dateB = b instanceof Date;
      if (dateA != dateB) return false;
      if (dateA && dateB) return a.getTime() == b.getTime();
      var regexpA = a instanceof RegExp,
          regexpB = b instanceof RegExp;
      if (regexpA != regexpB) return false;
      if (regexpA && regexpB) return a.toString() == b.toString();
      var keys = keyList(a);
      length = keys.length;

      if (length !== keyList(b).length) {
        return false;
      }

      for (i = length; i-- !== 0;) {
        if (!hasProp.call(b, keys[i])) return false;
      } // end fast-deep-equal
      // Custom handling for React


      for (i = length; i-- !== 0;) {
        key = keys[i];

        if (key === '_owner' && a.$$typeof) {
          // React-specific: avoid traversing React elements' _owner.
          //  _owner contains circular references
          // and is not needed when comparing the actual elements (and not their owners)
          // .$$typeof and ._store on just reasonable markers of a react element
          continue;
        } else {
          // all other properties should be traversed as usual
          if (!equal(a[key], b[key])) return false;
        }
      } // fast-deep-equal index.js 2.0.1


      return true;
    }

    return a !== a && b !== b;
  } // end fast-deep-equal


  function exportedEqual(a, b) {
    try {
      return equal(a, b);
    } catch (error) {
      if (error.message && error.message.match(/stack|recursion/i)) {
        // warn on circular references, don't crash
        // browsers give this different errors name and messages:
        // chrome/safari: "RangeError", "Maximum call stack size exceeded"
        // firefox: "InternalError", too much recursion"
        // edge: "Error", "Out of stack space"
        console.warn('Warning: react-fast-compare does not handle circular references.', error.name, error.message);
        return false;
      } // some other error. we should definitely know about these


      throw error;
    }
  }

  function _extends$1$1() { _extends$1$1 = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; }; return _extends$1$1.apply(this, arguments); }
  var containerCSS = function containerCSS(_ref) {
    var isDisabled = _ref.isDisabled,
        isRtl = _ref.isRtl;
    return {
      label: 'container',
      direction: isRtl ? 'rtl' : null,
      pointerEvents: isDisabled ? 'none' : null,
      // cancel mouse events when disabled
      position: 'relative'
    };
  };
  var SelectContainer = function SelectContainer(props) {
    var children = props.children,
        className = props.className,
        cx = props.cx,
        getStyles = props.getStyles,
        innerProps = props.innerProps,
        isDisabled = props.isDisabled,
        isRtl = props.isRtl;
    return core.jsx("div", _extends$1$1({
      css: getStyles('container', props),
      className: cx({
        '--is-disabled': isDisabled,
        '--is-rtl': isRtl
      }, className)
    }, innerProps), children);
  }; // ==============================
  // Value Container
  // ==============================

  var valueContainerCSS = function valueContainerCSS(_ref2) {
    var spacing = _ref2.theme.spacing;
    return {
      alignItems: 'center',
      display: 'flex',
      flex: 1,
      flexWrap: 'wrap',
      padding: spacing.baseUnit / 2 + "px " + spacing.baseUnit * 2 + "px",
      WebkitOverflowScrolling: 'touch',
      position: 'relative',
      overflow: 'hidden'
    };
  };
  var ValueContainer = function ValueContainer(props) {
    var children = props.children,
        className = props.className,
        cx = props.cx,
        isMulti = props.isMulti,
        getStyles = props.getStyles,
        hasValue = props.hasValue;
    return core.jsx("div", {
      css: getStyles('valueContainer', props),
      className: cx({
        'value-container': true,
        'value-container--is-multi': isMulti,
        'value-container--has-value': hasValue
      }, className)
    }, children);
  }; // ==============================
  // Indicator Container
  // ==============================

  var indicatorsContainerCSS = function indicatorsContainerCSS() {
    return {
      alignItems: 'center',
      alignSelf: 'stretch',
      display: 'flex',
      flexShrink: 0
    };
  };
  var IndicatorsContainer = function IndicatorsContainer(props) {
    var children = props.children,
        className = props.className,
        cx = props.cx,
        getStyles = props.getStyles;
    return core.jsx("div", {
      css: getStyles('indicatorsContainer', props),
      className: cx({
        indicators: true
      }, className)
    }, children);
  };

  function _templateObject() {
    var data = _taggedTemplateLiteralLoose(["\n  0%, 80%, 100% { opacity: 0; }\n  40% { opacity: 1; }\n"]);

    _templateObject = function _templateObject() {
      return data;
    };

    return data;
  }

  function _taggedTemplateLiteralLoose(strings, raw) { if (!raw) { raw = strings.slice(0); } strings.raw = raw; return strings; }

  function _extends$2() { _extends$2 = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; }; return _extends$2.apply(this, arguments); }

  function _objectWithoutPropertiesLoose(source, excluded) { if (source == null) return {}; var target = {}; var sourceKeys = Object.keys(source); var key, i; for (i = 0; i < sourceKeys.length; i++) { key = sourceKeys[i]; if (excluded.indexOf(key) >= 0) continue; target[key] = source[key]; } return target; }

  var _ref2 = process.env.NODE_ENV === "production" ? {
    name: "19bqh2r",
    styles: "display:inline-block;fill:currentColor;line-height:1;stroke:currentColor;stroke-width:0;"
  } : {
    name: "19bqh2r",
    styles: "display:inline-block;fill:currentColor;line-height:1;stroke:currentColor;stroke-width:0;",
    map: "/*# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbImluZGljYXRvcnMuanMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBa0JJIiwiZmlsZSI6ImluZGljYXRvcnMuanMiLCJzb3VyY2VzQ29udGVudCI6WyIvLyBAZmxvd1xuLyoqIEBqc3gganN4ICovXG5pbXBvcnQgeyB0eXBlIE5vZGUgfSBmcm9tICdyZWFjdCc7XG5pbXBvcnQgeyBqc3gsIGtleWZyYW1lcyB9IGZyb20gJ0BlbW90aW9uL2NvcmUnO1xuXG5pbXBvcnQgdHlwZSB7IENvbW1vblByb3BzLCBUaGVtZSB9IGZyb20gJy4uL3R5cGVzJztcblxuLy8gPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09XG4vLyBEcm9wZG93biAmIENsZWFyIEljb25zXG4vLyA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT1cblxuY29uc3QgU3ZnID0gKHsgc2l6ZSwgLi4ucHJvcHMgfTogeyBzaXplOiBudW1iZXIgfSkgPT4gKFxuICA8c3ZnXG4gICAgaGVpZ2h0PXtzaXplfVxuICAgIHdpZHRoPXtzaXplfVxuICAgIHZpZXdCb3g9XCIwIDAgMjAgMjBcIlxuICAgIGFyaWEtaGlkZGVuPVwidHJ1ZVwiXG4gICAgZm9jdXNhYmxlPVwiZmFsc2VcIlxuICAgIGNzcz17e1xuICAgICAgZGlzcGxheTogJ2lubGluZS1ibG9jaycsXG4gICAgICBmaWxsOiAnY3VycmVudENvbG9yJyxcbiAgICAgIGxpbmVIZWlnaHQ6IDEsXG4gICAgICBzdHJva2U6ICdjdXJyZW50Q29sb3InLFxuICAgICAgc3Ryb2tlV2lkdGg6IDAsXG4gICAgfX1cbiAgICB7Li4ucHJvcHN9XG4gIC8+XG4pO1xuXG5leHBvcnQgY29uc3QgQ3Jvc3NJY29uID0gKHByb3BzOiBhbnkpID0+IChcbiAgPFN2ZyBzaXplPXsyMH0gey4uLnByb3BzfT5cbiAgICA8cGF0aCBkPVwiTTE0LjM0OCAxNC44NDljLTAuNDY5IDAuNDY5LTEuMjI5IDAuNDY5LTEuNjk3IDBsLTIuNjUxLTMuMDMwLTIuNjUxIDMuMDI5Yy0wLjQ2OSAwLjQ2OS0xLjIyOSAwLjQ2OS0xLjY5NyAwLTAuNDY5LTAuNDY5LTAuNDY5LTEuMjI5IDAtMS42OTdsMi43NTgtMy4xNS0yLjc1OS0zLjE1MmMtMC40NjktMC40NjktMC40NjktMS4yMjggMC0xLjY5N3MxLjIyOC0wLjQ2OSAxLjY5NyAwbDIuNjUyIDMuMDMxIDIuNjUxLTMuMDMxYzAuNDY5LTAuNDY5IDEuMjI4LTAuNDY5IDEuNjk3IDBzMC40NjkgMS4yMjkgMCAxLjY5N2wtMi43NTggMy4xNTIgMi43NTggMy4xNWMwLjQ2OSAwLjQ2OSAwLjQ2OSAxLjIyOSAwIDEuNjk4elwiIC8+XG4gIDwvU3ZnPlxuKTtcbmV4cG9ydCBjb25zdCBEb3duQ2hldnJvbiA9IChwcm9wczogYW55KSA9PiAoXG4gIDxTdmcgc2l6ZT17MjB9IHsuLi5wcm9wc30+XG4gICAgPHBhdGggZD1cIk00LjUxNiA3LjU0OGMwLjQzNi0wLjQ0NiAxLjA0My0wLjQ4MSAxLjU3NiAwbDMuOTA4IDMuNzQ3IDMuOTA4LTMuNzQ3YzAuNTMzLTAuNDgxIDEuMTQxLTAuNDQ2IDEuNTc0IDAgMC40MzYgMC40NDUgMC40MDggMS4xOTcgMCAxLjYxNS0wLjQwNiAwLjQxOC00LjY5NSA0LjUwMi00LjY5NSA0LjUwMi0wLjIxNyAwLjIyMy0wLjUwMiAwLjMzNS0wLjc4NyAwLjMzNXMtMC41Ny0wLjExMi0wLjc4OS0wLjMzNWMwIDAtNC4yODctNC4wODQtNC42OTUtNC41MDJzLTAuNDM2LTEuMTcgMC0xLjYxNXpcIiAvPlxuICA8L1N2Zz5cbik7XG5cbi8vID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PVxuLy8gRHJvcGRvd24gJiBDbGVhciBCdXR0b25zXG4vLyA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT1cblxuZXhwb3J0IHR5cGUgSW5kaWNhdG9yUHJvcHMgPSBDb21tb25Qcm9wcyAmIHtcbiAgLyoqIFRoZSBjaGlsZHJlbiB0byBiZSByZW5kZXJlZCBpbnNpZGUgdGhlIGluZGljYXRvci4gKi9cbiAgY2hpbGRyZW46IE5vZGUsXG4gIC8qKiBQcm9wcyB0aGF0IHdpbGwgYmUgcGFzc2VkIG9uIHRvIHRoZSBjaGlsZHJlbi4gKi9cbiAgaW5uZXJQcm9wczogYW55LFxuICAvKiogVGhlIGZvY3VzZWQgc3RhdGUgb2YgdGhlIHNlbGVjdC4gKi9cbiAgaXNGb2N1c2VkOiBib29sZWFuLFxuICAvKiogV2hldGhlciB0aGUgdGV4dCBpcyByaWdodCB0byBsZWZ0ICovXG4gIGlzUnRsOiBib29sZWFuLFxufTtcblxuY29uc3QgYmFzZUNTUyA9ICh7XG4gIGlzRm9jdXNlZCxcbiAgdGhlbWU6IHtcbiAgICBzcGFjaW5nOiB7IGJhc2VVbml0IH0sXG4gICAgY29sb3JzLFxuICB9LFxufTogSW5kaWNhdG9yUHJvcHMpID0+ICh7XG4gIGxhYmVsOiAnaW5kaWNhdG9yQ29udGFpbmVyJyxcbiAgY29sb3I6IGlzRm9jdXNlZCA/IGNvbG9ycy5uZXV0cmFsNjAgOiBjb2xvcnMubmV1dHJhbDIwLFxuICBkaXNwbGF5OiAnZmxleCcsXG4gIHBhZGRpbmc6IGJhc2VVbml0ICogMixcbiAgdHJhbnNpdGlvbjogJ2NvbG9yIDE1MG1zJyxcblxuICAnOmhvdmVyJzoge1xuICAgIGNvbG9yOiBpc0ZvY3VzZWQgPyBjb2xvcnMubmV1dHJhbDgwIDogY29sb3JzLm5ldXRyYWw0MCxcbiAgfSxcbn0pO1xuXG5leHBvcnQgY29uc3QgZHJvcGRvd25JbmRpY2F0b3JDU1MgPSBiYXNlQ1NTO1xuZXhwb3J0IGNvbnN0IERyb3Bkb3duSW5kaWNhdG9yID0gKHByb3BzOiBJbmRpY2F0b3JQcm9wcykgPT4ge1xuICBjb25zdCB7IGNoaWxkcmVuLCBjbGFzc05hbWUsIGN4LCBnZXRTdHlsZXMsIGlubmVyUHJvcHMgfSA9IHByb3BzO1xuICByZXR1cm4gKFxuICAgIDxkaXZcbiAgICAgIHsuLi5pbm5lclByb3BzfVxuICAgICAgY3NzPXtnZXRTdHlsZXMoJ2Ryb3Bkb3duSW5kaWNhdG9yJywgcHJvcHMpfVxuICAgICAgY2xhc3NOYW1lPXtjeChcbiAgICAgICAge1xuICAgICAgICAgIGluZGljYXRvcjogdHJ1ZSxcbiAgICAgICAgICAnZHJvcGRvd24taW5kaWNhdG9yJzogdHJ1ZSxcbiAgICAgICAgfSxcbiAgICAgICAgY2xhc3NOYW1lXG4gICAgICApfVxuICAgID5cbiAgICAgIHtjaGlsZHJlbiB8fCA8RG93bkNoZXZyb24gLz59XG4gICAgPC9kaXY+XG4gICk7XG59O1xuXG5leHBvcnQgY29uc3QgY2xlYXJJbmRpY2F0b3JDU1MgPSBiYXNlQ1NTO1xuZXhwb3J0IGNvbnN0IENsZWFySW5kaWNhdG9yID0gKHByb3BzOiBJbmRpY2F0b3JQcm9wcykgPT4ge1xuICBjb25zdCB7IGNoaWxkcmVuLCBjbGFzc05hbWUsIGN4LCBnZXRTdHlsZXMsIGlubmVyUHJvcHMgfSA9IHByb3BzO1xuICByZXR1cm4gKFxuICAgIDxkaXZcbiAgICAgIHsuLi5pbm5lclByb3BzfVxuICAgICAgY3NzPXtnZXRTdHlsZXMoJ2NsZWFySW5kaWNhdG9yJywgcHJvcHMpfVxuICAgICAgY2xhc3NOYW1lPXtjeChcbiAgICAgICAge1xuICAgICAgICAgIGluZGljYXRvcjogdHJ1ZSxcbiAgICAgICAgICAnY2xlYXItaW5kaWNhdG9yJzogdHJ1ZSxcbiAgICAgICAgfSxcbiAgICAgICAgY2xhc3NOYW1lXG4gICAgICApfVxuICAgID5cbiAgICAgIHtjaGlsZHJlbiB8fCA8Q3Jvc3NJY29uIC8+fVxuICAgIDwvZGl2PlxuICApO1xufTtcblxuLy8gPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09XG4vLyBTZXBhcmF0b3Jcbi8vID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PVxuXG50eXBlIFNlcGFyYXRvclN0YXRlID0geyBpc0Rpc2FibGVkOiBib29sZWFuIH07XG5cbmV4cG9ydCBjb25zdCBpbmRpY2F0b3JTZXBhcmF0b3JDU1MgPSAoe1xuICBpc0Rpc2FibGVkLFxuICB0aGVtZToge1xuICAgIHNwYWNpbmc6IHsgYmFzZVVuaXQgfSxcbiAgICBjb2xvcnMsXG4gIH0sXG59OiBDb21tb25Qcm9wcyAmIFNlcGFyYXRvclN0YXRlKSA9PiAoe1xuICBsYWJlbDogJ2luZGljYXRvclNlcGFyYXRvcicsXG4gIGFsaWduU2VsZjogJ3N0cmV0Y2gnLFxuICBiYWNrZ3JvdW5kQ29sb3I6IGlzRGlzYWJsZWQgPyBjb2xvcnMubmV1dHJhbDEwIDogY29sb3JzLm5ldXRyYWwyMCxcbiAgbWFyZ2luQm90dG9tOiBiYXNlVW5pdCAqIDIsXG4gIG1hcmdpblRvcDogYmFzZVVuaXQgKiAyLFxuICB3aWR0aDogMSxcbn0pO1xuXG5leHBvcnQgY29uc3QgSW5kaWNhdG9yU2VwYXJhdG9yID0gKHByb3BzOiBJbmRpY2F0b3JQcm9wcykgPT4ge1xuICBjb25zdCB7IGNsYXNzTmFtZSwgY3gsIGdldFN0eWxlcywgaW5uZXJQcm9wcyB9ID0gcHJvcHM7XG4gIHJldHVybiAoXG4gICAgPHNwYW5cbiAgICAgIHsuLi5pbm5lclByb3BzfVxuICAgICAgY3NzPXtnZXRTdHlsZXMoJ2luZGljYXRvclNlcGFyYXRvcicsIHByb3BzKX1cbiAgICAgIGNsYXNzTmFtZT17Y3goeyAnaW5kaWNhdG9yLXNlcGFyYXRvcic6IHRydWUgfSwgY2xhc3NOYW1lKX1cbiAgICAvPlxuICApO1xufTtcblxuLy8gPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09XG4vLyBMb2FkaW5nXG4vLyA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT1cblxuY29uc3QgbG9hZGluZ0RvdEFuaW1hdGlvbnMgPSBrZXlmcmFtZXNgXG4gIDAlLCA4MCUsIDEwMCUgeyBvcGFjaXR5OiAwOyB9XG4gIDQwJSB7IG9wYWNpdHk6IDE7IH1cbmA7XG5cbmV4cG9ydCBjb25zdCBsb2FkaW5nSW5kaWNhdG9yQ1NTID0gKHtcbiAgaXNGb2N1c2VkLFxuICBzaXplLFxuICB0aGVtZToge1xuICAgIGNvbG9ycyxcbiAgICBzcGFjaW5nOiB7IGJhc2VVbml0IH0sXG4gIH0sXG59OiB7XG4gIGlzRm9jdXNlZDogYm9vbGVhbixcbiAgc2l6ZTogbnVtYmVyLFxuICB0aGVtZTogVGhlbWUsXG59KSA9PiAoe1xuICBsYWJlbDogJ2xvYWRpbmdJbmRpY2F0b3InLFxuICBjb2xvcjogaXNGb2N1c2VkID8gY29sb3JzLm5ldXRyYWw2MCA6IGNvbG9ycy5uZXV0cmFsMjAsXG4gIGRpc3BsYXk6ICdmbGV4JyxcbiAgcGFkZGluZzogYmFzZVVuaXQgKiAyLFxuICB0cmFuc2l0aW9uOiAnY29sb3IgMTUwbXMnLFxuICBhbGlnblNlbGY6ICdjZW50ZXInLFxuICBmb250U2l6ZTogc2l6ZSxcbiAgbGluZUhlaWdodDogMSxcbiAgbWFyZ2luUmlnaHQ6IHNpemUsXG4gIHRleHRBbGlnbjogJ2NlbnRlcicsXG4gIHZlcnRpY2FsQWxpZ246ICdtaWRkbGUnLFxufSk7XG5cbnR5cGUgRG90UHJvcHMgPSB7IGRlbGF5OiBudW1iZXIsIG9mZnNldDogYm9vbGVhbiB9O1xuY29uc3QgTG9hZGluZ0RvdCA9ICh7IGRlbGF5LCBvZmZzZXQgfTogRG90UHJvcHMpID0+IChcbiAgPHNwYW5cbiAgICBjc3M9e3tcbiAgICAgIGFuaW1hdGlvbjogYCR7bG9hZGluZ0RvdEFuaW1hdGlvbnN9IDFzIGVhc2UtaW4tb3V0ICR7ZGVsYXl9bXMgaW5maW5pdGU7YCxcbiAgICAgIGJhY2tncm91bmRDb2xvcjogJ2N1cnJlbnRDb2xvcicsXG4gICAgICBib3JkZXJSYWRpdXM6ICcxZW0nLFxuICAgICAgZGlzcGxheTogJ2lubGluZS1ibG9jaycsXG4gICAgICBtYXJnaW5MZWZ0OiBvZmZzZXQgPyAnMWVtJyA6IG51bGwsXG4gICAgICBoZWlnaHQ6ICcxZW0nLFxuICAgICAgdmVydGljYWxBbGlnbjogJ3RvcCcsXG4gICAgICB3aWR0aDogJzFlbScsXG4gICAgfX1cbiAgLz5cbik7XG5cbmV4cG9ydCB0eXBlIExvYWRpbmdJY29uUHJvcHMgPSB7XG4gIC8qKiBQcm9wcyB0aGF0IHdpbGwgYmUgcGFzc2VkIG9uIHRvIHRoZSBjaGlsZHJlbi4gKi9cbiAgaW5uZXJQcm9wczogYW55LFxuICAvKiogVGhlIGZvY3VzZWQgc3RhdGUgb2YgdGhlIHNlbGVjdC4gKi9cbiAgaXNGb2N1c2VkOiBib29sZWFuLFxuICAvKiogV2hldGhlciB0aGUgdGV4dCBpcyByaWdodCB0byBsZWZ0ICovXG4gIGlzUnRsOiBib29sZWFuLFxufSAmIENvbW1vblByb3BzICYge1xuICAgIC8qKiBTZXQgc2l6ZSBvZiB0aGUgY29udGFpbmVyLiAqL1xuICAgIHNpemU6IG51bWJlcixcbiAgfTtcbmV4cG9ydCBjb25zdCBMb2FkaW5nSW5kaWNhdG9yID0gKHByb3BzOiBMb2FkaW5nSWNvblByb3BzKSA9PiB7XG4gIGNvbnN0IHsgY2xhc3NOYW1lLCBjeCwgZ2V0U3R5bGVzLCBpbm5lclByb3BzLCBpc1J0bCB9ID0gcHJvcHM7XG5cbiAgcmV0dXJuIChcbiAgICA8ZGl2XG4gICAgICB7Li4uaW5uZXJQcm9wc31cbiAgICAgIGNzcz17Z2V0U3R5bGVzKCdsb2FkaW5nSW5kaWNhdG9yJywgcHJvcHMpfVxuICAgICAgY2xhc3NOYW1lPXtjeChcbiAgICAgICAge1xuICAgICAgICAgIGluZGljYXRvcjogdHJ1ZSxcbiAgICAgICAgICAnbG9hZGluZy1pbmRpY2F0b3InOiB0cnVlLFxuICAgICAgICB9LFxuICAgICAgICBjbGFzc05hbWVcbiAgICAgICl9XG4gICAgPlxuICAgICAgPExvYWRpbmdEb3QgZGVsYXk9ezB9IG9mZnNldD17aXNSdGx9IC8+XG4gICAgICA8TG9hZGluZ0RvdCBkZWxheT17MTYwfSBvZmZzZXQgLz5cbiAgICAgIDxMb2FkaW5nRG90IGRlbGF5PXszMjB9IG9mZnNldD17IWlzUnRsfSAvPlxuICAgIDwvZGl2PlxuICApO1xufTtcbkxvYWRpbmdJbmRpY2F0b3IuZGVmYXVsdFByb3BzID0geyBzaXplOiA0IH07XG4iXX0= */"
  };

  // ==============================
  // Dropdown & Clear Icons
  // ==============================
  var Svg = function Svg(_ref) {
    var size = _ref.size,
        props = _objectWithoutPropertiesLoose(_ref, ["size"]);

    return core.jsx("svg", _extends$2({
      height: size,
      width: size,
      viewBox: "0 0 20 20",
      "aria-hidden": "true",
      focusable: "false",
      css: _ref2
    }, props));
  };

  var CrossIcon = function CrossIcon(props) {
    return core.jsx(Svg, _extends$2({
      size: 20
    }, props), core.jsx("path", {
      d: "M14.348 14.849c-0.469 0.469-1.229 0.469-1.697 0l-2.651-3.030-2.651 3.029c-0.469 0.469-1.229 0.469-1.697 0-0.469-0.469-0.469-1.229 0-1.697l2.758-3.15-2.759-3.152c-0.469-0.469-0.469-1.228 0-1.697s1.228-0.469 1.697 0l2.652 3.031 2.651-3.031c0.469-0.469 1.228-0.469 1.697 0s0.469 1.229 0 1.697l-2.758 3.152 2.758 3.15c0.469 0.469 0.469 1.229 0 1.698z"
    }));
  };
  var DownChevron = function DownChevron(props) {
    return core.jsx(Svg, _extends$2({
      size: 20
    }, props), core.jsx("path", {
      d: "M4.516 7.548c0.436-0.446 1.043-0.481 1.576 0l3.908 3.747 3.908-3.747c0.533-0.481 1.141-0.446 1.574 0 0.436 0.445 0.408 1.197 0 1.615-0.406 0.418-4.695 4.502-4.695 4.502-0.217 0.223-0.502 0.335-0.787 0.335s-0.57-0.112-0.789-0.335c0 0-4.287-4.084-4.695-4.502s-0.436-1.17 0-1.615z"
    }));
  }; // ==============================
  // Dropdown & Clear Buttons
  // ==============================

  var baseCSS = function baseCSS(_ref3) {
    var isFocused = _ref3.isFocused,
        _ref3$theme = _ref3.theme,
        baseUnit = _ref3$theme.spacing.baseUnit,
        colors = _ref3$theme.colors;
    return {
      label: 'indicatorContainer',
      color: isFocused ? colors.neutral60 : colors.neutral20,
      display: 'flex',
      padding: baseUnit * 2,
      transition: 'color 150ms',
      ':hover': {
        color: isFocused ? colors.neutral80 : colors.neutral40
      }
    };
  };

  var dropdownIndicatorCSS = baseCSS;
  var DropdownIndicator = function DropdownIndicator(props) {
    var children = props.children,
        className = props.className,
        cx = props.cx,
        getStyles = props.getStyles,
        innerProps = props.innerProps;
    return core.jsx("div", _extends$2({}, innerProps, {
      css: getStyles('dropdownIndicator', props),
      className: cx({
        indicator: true,
        'dropdown-indicator': true
      }, className)
    }), children || core.jsx(DownChevron, null));
  };
  var clearIndicatorCSS = baseCSS;
  var ClearIndicator = function ClearIndicator(props) {
    var children = props.children,
        className = props.className,
        cx = props.cx,
        getStyles = props.getStyles,
        innerProps = props.innerProps;
    return core.jsx("div", _extends$2({}, innerProps, {
      css: getStyles('clearIndicator', props),
      className: cx({
        indicator: true,
        'clear-indicator': true
      }, className)
    }), children || core.jsx(CrossIcon, null));
  }; // ==============================
  // Separator
  // ==============================

  var indicatorSeparatorCSS = function indicatorSeparatorCSS(_ref4) {
    var isDisabled = _ref4.isDisabled,
        _ref4$theme = _ref4.theme,
        baseUnit = _ref4$theme.spacing.baseUnit,
        colors = _ref4$theme.colors;
    return {
      label: 'indicatorSeparator',
      alignSelf: 'stretch',
      backgroundColor: isDisabled ? colors.neutral10 : colors.neutral20,
      marginBottom: baseUnit * 2,
      marginTop: baseUnit * 2,
      width: 1
    };
  };
  var IndicatorSeparator = function IndicatorSeparator(props) {
    var className = props.className,
        cx = props.cx,
        getStyles = props.getStyles,
        innerProps = props.innerProps;
    return core.jsx("span", _extends$2({}, innerProps, {
      css: getStyles('indicatorSeparator', props),
      className: cx({
        'indicator-separator': true
      }, className)
    }));
  }; // ==============================
  // Loading
  // ==============================

  var loadingDotAnimations = core.keyframes(_templateObject());
  var loadingIndicatorCSS = function loadingIndicatorCSS(_ref5) {
    var isFocused = _ref5.isFocused,
        size = _ref5.size,
        _ref5$theme = _ref5.theme,
        colors = _ref5$theme.colors,
        baseUnit = _ref5$theme.spacing.baseUnit;
    return {
      label: 'loadingIndicator',
      color: isFocused ? colors.neutral60 : colors.neutral20,
      display: 'flex',
      padding: baseUnit * 2,
      transition: 'color 150ms',
      alignSelf: 'center',
      fontSize: size,
      lineHeight: 1,
      marginRight: size,
      textAlign: 'center',
      verticalAlign: 'middle'
    };
  };

  var LoadingDot = function LoadingDot(_ref6) {
    var delay = _ref6.delay,
        offset = _ref6.offset;
    return core.jsx("span", {
      css:
      /*#__PURE__*/
      css({
        animation: loadingDotAnimations + " 1s ease-in-out " + delay + "ms infinite;",
        backgroundColor: 'currentColor',
        borderRadius: '1em',
        display: 'inline-block',
        marginLeft: offset ? '1em' : null,
        height: '1em',
        verticalAlign: 'top',
        width: '1em'
      }, process.env.NODE_ENV === "production" ? "" : "/*# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbImluZGljYXRvcnMuanMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBc0xJIiwiZmlsZSI6ImluZGljYXRvcnMuanMiLCJzb3VyY2VzQ29udGVudCI6WyIvLyBAZmxvd1xuLyoqIEBqc3gganN4ICovXG5pbXBvcnQgeyB0eXBlIE5vZGUgfSBmcm9tICdyZWFjdCc7XG5pbXBvcnQgeyBqc3gsIGtleWZyYW1lcyB9IGZyb20gJ0BlbW90aW9uL2NvcmUnO1xuXG5pbXBvcnQgdHlwZSB7IENvbW1vblByb3BzLCBUaGVtZSB9IGZyb20gJy4uL3R5cGVzJztcblxuLy8gPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09XG4vLyBEcm9wZG93biAmIENsZWFyIEljb25zXG4vLyA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT1cblxuY29uc3QgU3ZnID0gKHsgc2l6ZSwgLi4ucHJvcHMgfTogeyBzaXplOiBudW1iZXIgfSkgPT4gKFxuICA8c3ZnXG4gICAgaGVpZ2h0PXtzaXplfVxuICAgIHdpZHRoPXtzaXplfVxuICAgIHZpZXdCb3g9XCIwIDAgMjAgMjBcIlxuICAgIGFyaWEtaGlkZGVuPVwidHJ1ZVwiXG4gICAgZm9jdXNhYmxlPVwiZmFsc2VcIlxuICAgIGNzcz17e1xuICAgICAgZGlzcGxheTogJ2lubGluZS1ibG9jaycsXG4gICAgICBmaWxsOiAnY3VycmVudENvbG9yJyxcbiAgICAgIGxpbmVIZWlnaHQ6IDEsXG4gICAgICBzdHJva2U6ICdjdXJyZW50Q29sb3InLFxuICAgICAgc3Ryb2tlV2lkdGg6IDAsXG4gICAgfX1cbiAgICB7Li4ucHJvcHN9XG4gIC8+XG4pO1xuXG5leHBvcnQgY29uc3QgQ3Jvc3NJY29uID0gKHByb3BzOiBhbnkpID0+IChcbiAgPFN2ZyBzaXplPXsyMH0gey4uLnByb3BzfT5cbiAgICA8cGF0aCBkPVwiTTE0LjM0OCAxNC44NDljLTAuNDY5IDAuNDY5LTEuMjI5IDAuNDY5LTEuNjk3IDBsLTIuNjUxLTMuMDMwLTIuNjUxIDMuMDI5Yy0wLjQ2OSAwLjQ2OS0xLjIyOSAwLjQ2OS0xLjY5NyAwLTAuNDY5LTAuNDY5LTAuNDY5LTEuMjI5IDAtMS42OTdsMi43NTgtMy4xNS0yLjc1OS0zLjE1MmMtMC40NjktMC40NjktMC40NjktMS4yMjggMC0xLjY5N3MxLjIyOC0wLjQ2OSAxLjY5NyAwbDIuNjUyIDMuMDMxIDIuNjUxLTMuMDMxYzAuNDY5LTAuNDY5IDEuMjI4LTAuNDY5IDEuNjk3IDBzMC40NjkgMS4yMjkgMCAxLjY5N2wtMi43NTggMy4xNTIgMi43NTggMy4xNWMwLjQ2OSAwLjQ2OSAwLjQ2OSAxLjIyOSAwIDEuNjk4elwiIC8+XG4gIDwvU3ZnPlxuKTtcbmV4cG9ydCBjb25zdCBEb3duQ2hldnJvbiA9IChwcm9wczogYW55KSA9PiAoXG4gIDxTdmcgc2l6ZT17MjB9IHsuLi5wcm9wc30+XG4gICAgPHBhdGggZD1cIk00LjUxNiA3LjU0OGMwLjQzNi0wLjQ0NiAxLjA0My0wLjQ4MSAxLjU3NiAwbDMuOTA4IDMuNzQ3IDMuOTA4LTMuNzQ3YzAuNTMzLTAuNDgxIDEuMTQxLTAuNDQ2IDEuNTc0IDAgMC40MzYgMC40NDUgMC40MDggMS4xOTcgMCAxLjYxNS0wLjQwNiAwLjQxOC00LjY5NSA0LjUwMi00LjY5NSA0LjUwMi0wLjIxNyAwLjIyMy0wLjUwMiAwLjMzNS0wLjc4NyAwLjMzNXMtMC41Ny0wLjExMi0wLjc4OS0wLjMzNWMwIDAtNC4yODctNC4wODQtNC42OTUtNC41MDJzLTAuNDM2LTEuMTcgMC0xLjYxNXpcIiAvPlxuICA8L1N2Zz5cbik7XG5cbi8vID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PVxuLy8gRHJvcGRvd24gJiBDbGVhciBCdXR0b25zXG4vLyA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT1cblxuZXhwb3J0IHR5cGUgSW5kaWNhdG9yUHJvcHMgPSBDb21tb25Qcm9wcyAmIHtcbiAgLyoqIFRoZSBjaGlsZHJlbiB0byBiZSByZW5kZXJlZCBpbnNpZGUgdGhlIGluZGljYXRvci4gKi9cbiAgY2hpbGRyZW46IE5vZGUsXG4gIC8qKiBQcm9wcyB0aGF0IHdpbGwgYmUgcGFzc2VkIG9uIHRvIHRoZSBjaGlsZHJlbi4gKi9cbiAgaW5uZXJQcm9wczogYW55LFxuICAvKiogVGhlIGZvY3VzZWQgc3RhdGUgb2YgdGhlIHNlbGVjdC4gKi9cbiAgaXNGb2N1c2VkOiBib29sZWFuLFxuICAvKiogV2hldGhlciB0aGUgdGV4dCBpcyByaWdodCB0byBsZWZ0ICovXG4gIGlzUnRsOiBib29sZWFuLFxufTtcblxuY29uc3QgYmFzZUNTUyA9ICh7XG4gIGlzRm9jdXNlZCxcbiAgdGhlbWU6IHtcbiAgICBzcGFjaW5nOiB7IGJhc2VVbml0IH0sXG4gICAgY29sb3JzLFxuICB9LFxufTogSW5kaWNhdG9yUHJvcHMpID0+ICh7XG4gIGxhYmVsOiAnaW5kaWNhdG9yQ29udGFpbmVyJyxcbiAgY29sb3I6IGlzRm9jdXNlZCA/IGNvbG9ycy5uZXV0cmFsNjAgOiBjb2xvcnMubmV1dHJhbDIwLFxuICBkaXNwbGF5OiAnZmxleCcsXG4gIHBhZGRpbmc6IGJhc2VVbml0ICogMixcbiAgdHJhbnNpdGlvbjogJ2NvbG9yIDE1MG1zJyxcblxuICAnOmhvdmVyJzoge1xuICAgIGNvbG9yOiBpc0ZvY3VzZWQgPyBjb2xvcnMubmV1dHJhbDgwIDogY29sb3JzLm5ldXRyYWw0MCxcbiAgfSxcbn0pO1xuXG5leHBvcnQgY29uc3QgZHJvcGRvd25JbmRpY2F0b3JDU1MgPSBiYXNlQ1NTO1xuZXhwb3J0IGNvbnN0IERyb3Bkb3duSW5kaWNhdG9yID0gKHByb3BzOiBJbmRpY2F0b3JQcm9wcykgPT4ge1xuICBjb25zdCB7IGNoaWxkcmVuLCBjbGFzc05hbWUsIGN4LCBnZXRTdHlsZXMsIGlubmVyUHJvcHMgfSA9IHByb3BzO1xuICByZXR1cm4gKFxuICAgIDxkaXZcbiAgICAgIHsuLi5pbm5lclByb3BzfVxuICAgICAgY3NzPXtnZXRTdHlsZXMoJ2Ryb3Bkb3duSW5kaWNhdG9yJywgcHJvcHMpfVxuICAgICAgY2xhc3NOYW1lPXtjeChcbiAgICAgICAge1xuICAgICAgICAgIGluZGljYXRvcjogdHJ1ZSxcbiAgICAgICAgICAnZHJvcGRvd24taW5kaWNhdG9yJzogdHJ1ZSxcbiAgICAgICAgfSxcbiAgICAgICAgY2xhc3NOYW1lXG4gICAgICApfVxuICAgID5cbiAgICAgIHtjaGlsZHJlbiB8fCA8RG93bkNoZXZyb24gLz59XG4gICAgPC9kaXY+XG4gICk7XG59O1xuXG5leHBvcnQgY29uc3QgY2xlYXJJbmRpY2F0b3JDU1MgPSBiYXNlQ1NTO1xuZXhwb3J0IGNvbnN0IENsZWFySW5kaWNhdG9yID0gKHByb3BzOiBJbmRpY2F0b3JQcm9wcykgPT4ge1xuICBjb25zdCB7IGNoaWxkcmVuLCBjbGFzc05hbWUsIGN4LCBnZXRTdHlsZXMsIGlubmVyUHJvcHMgfSA9IHByb3BzO1xuICByZXR1cm4gKFxuICAgIDxkaXZcbiAgICAgIHsuLi5pbm5lclByb3BzfVxuICAgICAgY3NzPXtnZXRTdHlsZXMoJ2NsZWFySW5kaWNhdG9yJywgcHJvcHMpfVxuICAgICAgY2xhc3NOYW1lPXtjeChcbiAgICAgICAge1xuICAgICAgICAgIGluZGljYXRvcjogdHJ1ZSxcbiAgICAgICAgICAnY2xlYXItaW5kaWNhdG9yJzogdHJ1ZSxcbiAgICAgICAgfSxcbiAgICAgICAgY2xhc3NOYW1lXG4gICAgICApfVxuICAgID5cbiAgICAgIHtjaGlsZHJlbiB8fCA8Q3Jvc3NJY29uIC8+fVxuICAgIDwvZGl2PlxuICApO1xufTtcblxuLy8gPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09XG4vLyBTZXBhcmF0b3Jcbi8vID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PVxuXG50eXBlIFNlcGFyYXRvclN0YXRlID0geyBpc0Rpc2FibGVkOiBib29sZWFuIH07XG5cbmV4cG9ydCBjb25zdCBpbmRpY2F0b3JTZXBhcmF0b3JDU1MgPSAoe1xuICBpc0Rpc2FibGVkLFxuICB0aGVtZToge1xuICAgIHNwYWNpbmc6IHsgYmFzZVVuaXQgfSxcbiAgICBjb2xvcnMsXG4gIH0sXG59OiBDb21tb25Qcm9wcyAmIFNlcGFyYXRvclN0YXRlKSA9PiAoe1xuICBsYWJlbDogJ2luZGljYXRvclNlcGFyYXRvcicsXG4gIGFsaWduU2VsZjogJ3N0cmV0Y2gnLFxuICBiYWNrZ3JvdW5kQ29sb3I6IGlzRGlzYWJsZWQgPyBjb2xvcnMubmV1dHJhbDEwIDogY29sb3JzLm5ldXRyYWwyMCxcbiAgbWFyZ2luQm90dG9tOiBiYXNlVW5pdCAqIDIsXG4gIG1hcmdpblRvcDogYmFzZVVuaXQgKiAyLFxuICB3aWR0aDogMSxcbn0pO1xuXG5leHBvcnQgY29uc3QgSW5kaWNhdG9yU2VwYXJhdG9yID0gKHByb3BzOiBJbmRpY2F0b3JQcm9wcykgPT4ge1xuICBjb25zdCB7IGNsYXNzTmFtZSwgY3gsIGdldFN0eWxlcywgaW5uZXJQcm9wcyB9ID0gcHJvcHM7XG4gIHJldHVybiAoXG4gICAgPHNwYW5cbiAgICAgIHsuLi5pbm5lclByb3BzfVxuICAgICAgY3NzPXtnZXRTdHlsZXMoJ2luZGljYXRvclNlcGFyYXRvcicsIHByb3BzKX1cbiAgICAgIGNsYXNzTmFtZT17Y3goeyAnaW5kaWNhdG9yLXNlcGFyYXRvcic6IHRydWUgfSwgY2xhc3NOYW1lKX1cbiAgICAvPlxuICApO1xufTtcblxuLy8gPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09XG4vLyBMb2FkaW5nXG4vLyA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT1cblxuY29uc3QgbG9hZGluZ0RvdEFuaW1hdGlvbnMgPSBrZXlmcmFtZXNgXG4gIDAlLCA4MCUsIDEwMCUgeyBvcGFjaXR5OiAwOyB9XG4gIDQwJSB7IG9wYWNpdHk6IDE7IH1cbmA7XG5cbmV4cG9ydCBjb25zdCBsb2FkaW5nSW5kaWNhdG9yQ1NTID0gKHtcbiAgaXNGb2N1c2VkLFxuICBzaXplLFxuICB0aGVtZToge1xuICAgIGNvbG9ycyxcbiAgICBzcGFjaW5nOiB7IGJhc2VVbml0IH0sXG4gIH0sXG59OiB7XG4gIGlzRm9jdXNlZDogYm9vbGVhbixcbiAgc2l6ZTogbnVtYmVyLFxuICB0aGVtZTogVGhlbWUsXG59KSA9PiAoe1xuICBsYWJlbDogJ2xvYWRpbmdJbmRpY2F0b3InLFxuICBjb2xvcjogaXNGb2N1c2VkID8gY29sb3JzLm5ldXRyYWw2MCA6IGNvbG9ycy5uZXV0cmFsMjAsXG4gIGRpc3BsYXk6ICdmbGV4JyxcbiAgcGFkZGluZzogYmFzZVVuaXQgKiAyLFxuICB0cmFuc2l0aW9uOiAnY29sb3IgMTUwbXMnLFxuICBhbGlnblNlbGY6ICdjZW50ZXInLFxuICBmb250U2l6ZTogc2l6ZSxcbiAgbGluZUhlaWdodDogMSxcbiAgbWFyZ2luUmlnaHQ6IHNpemUsXG4gIHRleHRBbGlnbjogJ2NlbnRlcicsXG4gIHZlcnRpY2FsQWxpZ246ICdtaWRkbGUnLFxufSk7XG5cbnR5cGUgRG90UHJvcHMgPSB7IGRlbGF5OiBudW1iZXIsIG9mZnNldDogYm9vbGVhbiB9O1xuY29uc3QgTG9hZGluZ0RvdCA9ICh7IGRlbGF5LCBvZmZzZXQgfTogRG90UHJvcHMpID0+IChcbiAgPHNwYW5cbiAgICBjc3M9e3tcbiAgICAgIGFuaW1hdGlvbjogYCR7bG9hZGluZ0RvdEFuaW1hdGlvbnN9IDFzIGVhc2UtaW4tb3V0ICR7ZGVsYXl9bXMgaW5maW5pdGU7YCxcbiAgICAgIGJhY2tncm91bmRDb2xvcjogJ2N1cnJlbnRDb2xvcicsXG4gICAgICBib3JkZXJSYWRpdXM6ICcxZW0nLFxuICAgICAgZGlzcGxheTogJ2lubGluZS1ibG9jaycsXG4gICAgICBtYXJnaW5MZWZ0OiBvZmZzZXQgPyAnMWVtJyA6IG51bGwsXG4gICAgICBoZWlnaHQ6ICcxZW0nLFxuICAgICAgdmVydGljYWxBbGlnbjogJ3RvcCcsXG4gICAgICB3aWR0aDogJzFlbScsXG4gICAgfX1cbiAgLz5cbik7XG5cbmV4cG9ydCB0eXBlIExvYWRpbmdJY29uUHJvcHMgPSB7XG4gIC8qKiBQcm9wcyB0aGF0IHdpbGwgYmUgcGFzc2VkIG9uIHRvIHRoZSBjaGlsZHJlbi4gKi9cbiAgaW5uZXJQcm9wczogYW55LFxuICAvKiogVGhlIGZvY3VzZWQgc3RhdGUgb2YgdGhlIHNlbGVjdC4gKi9cbiAgaXNGb2N1c2VkOiBib29sZWFuLFxuICAvKiogV2hldGhlciB0aGUgdGV4dCBpcyByaWdodCB0byBsZWZ0ICovXG4gIGlzUnRsOiBib29sZWFuLFxufSAmIENvbW1vblByb3BzICYge1xuICAgIC8qKiBTZXQgc2l6ZSBvZiB0aGUgY29udGFpbmVyLiAqL1xuICAgIHNpemU6IG51bWJlcixcbiAgfTtcbmV4cG9ydCBjb25zdCBMb2FkaW5nSW5kaWNhdG9yID0gKHByb3BzOiBMb2FkaW5nSWNvblByb3BzKSA9PiB7XG4gIGNvbnN0IHsgY2xhc3NOYW1lLCBjeCwgZ2V0U3R5bGVzLCBpbm5lclByb3BzLCBpc1J0bCB9ID0gcHJvcHM7XG5cbiAgcmV0dXJuIChcbiAgICA8ZGl2XG4gICAgICB7Li4uaW5uZXJQcm9wc31cbiAgICAgIGNzcz17Z2V0U3R5bGVzKCdsb2FkaW5nSW5kaWNhdG9yJywgcHJvcHMpfVxuICAgICAgY2xhc3NOYW1lPXtjeChcbiAgICAgICAge1xuICAgICAgICAgIGluZGljYXRvcjogdHJ1ZSxcbiAgICAgICAgICAnbG9hZGluZy1pbmRpY2F0b3InOiB0cnVlLFxuICAgICAgICB9LFxuICAgICAgICBjbGFzc05hbWVcbiAgICAgICl9XG4gICAgPlxuICAgICAgPExvYWRpbmdEb3QgZGVsYXk9ezB9IG9mZnNldD17aXNSdGx9IC8+XG4gICAgICA8TG9hZGluZ0RvdCBkZWxheT17MTYwfSBvZmZzZXQgLz5cbiAgICAgIDxMb2FkaW5nRG90IGRlbGF5PXszMjB9IG9mZnNldD17IWlzUnRsfSAvPlxuICAgIDwvZGl2PlxuICApO1xufTtcbkxvYWRpbmdJbmRpY2F0b3IuZGVmYXVsdFByb3BzID0geyBzaXplOiA0IH07XG4iXX0= */")
    });
  };

  var LoadingIndicator = function LoadingIndicator(props) {
    var className = props.className,
        cx = props.cx,
        getStyles = props.getStyles,
        innerProps = props.innerProps,
        isRtl = props.isRtl;
    return core.jsx("div", _extends$2({}, innerProps, {
      css: getStyles('loadingIndicator', props),
      className: cx({
        indicator: true,
        'loading-indicator': true
      }, className)
    }), core.jsx(LoadingDot, {
      delay: 0,
      offset: isRtl
    }), core.jsx(LoadingDot, {
      delay: 160,
      offset: true
    }), core.jsx(LoadingDot, {
      delay: 320,
      offset: !isRtl
    }));
  };
  LoadingIndicator.defaultProps = {
    size: 4
  };

  function _extends$3() { _extends$3 = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; }; return _extends$3.apply(this, arguments); }
  var css$1 = function css(_ref) {
    var isDisabled = _ref.isDisabled,
        isFocused = _ref.isFocused,
        _ref$theme = _ref.theme,
        colors = _ref$theme.colors,
        borderRadius = _ref$theme.borderRadius,
        spacing = _ref$theme.spacing;
    return {
      label: 'control',
      alignItems: 'center',
      backgroundColor: isDisabled ? colors.neutral5 : colors.neutral0,
      borderColor: isDisabled ? colors.neutral10 : isFocused ? colors.primary : colors.neutral20,
      borderRadius: borderRadius,
      borderStyle: 'solid',
      borderWidth: 1,
      boxShadow: isFocused ? "0 0 0 1px " + colors.primary : null,
      cursor: 'default',
      display: 'flex',
      flexWrap: 'wrap',
      justifyContent: 'space-between',
      minHeight: spacing.controlHeight,
      outline: '0 !important',
      position: 'relative',
      transition: 'all 100ms',
      '&:hover': {
        borderColor: isFocused ? colors.primary : colors.neutral30
      }
    };
  };

  var Control = function Control(props) {
    var children = props.children,
        cx = props.cx,
        getStyles = props.getStyles,
        className = props.className,
        isDisabled = props.isDisabled,
        isFocused = props.isFocused,
        innerRef = props.innerRef,
        innerProps = props.innerProps,
        menuIsOpen = props.menuIsOpen;
    return core.jsx("div", _extends$3({
      ref: innerRef,
      css: getStyles('control', props),
      className: cx({
        control: true,
        'control--is-disabled': isDisabled,
        'control--is-focused': isFocused,
        'control--menu-is-open': menuIsOpen
      }, className)
    }, innerProps), children);
  };

  function _objectWithoutPropertiesLoose$1(source, excluded) { if (source == null) return {}; var target = {}; var sourceKeys = Object.keys(source); var key, i; for (i = 0; i < sourceKeys.length; i++) { key = sourceKeys[i]; if (excluded.indexOf(key) >= 0) continue; target[key] = source[key]; } return target; }

  function _extends$4() { _extends$4 = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; }; return _extends$4.apply(this, arguments); }
  var groupCSS = function groupCSS(_ref) {
    var spacing = _ref.theme.spacing;
    return {
      paddingBottom: spacing.baseUnit * 2,
      paddingTop: spacing.baseUnit * 2
    };
  };

  var Group = function Group(props) {
    var children = props.children,
        className = props.className,
        cx = props.cx,
        getStyles = props.getStyles,
        Heading = props.Heading,
        headingProps = props.headingProps,
        label = props.label,
        theme = props.theme,
        selectProps = props.selectProps;
    return core.jsx("div", {
      css: getStyles('group', props),
      className: cx({
        group: true
      }, className)
    }, core.jsx(Heading, _extends$4({}, headingProps, {
      selectProps: selectProps,
      theme: theme,
      getStyles: getStyles,
      cx: cx
    }), label), core.jsx("div", null, children));
  };

  var groupHeadingCSS = function groupHeadingCSS(_ref2) {
    var spacing = _ref2.theme.spacing;
    return {
      label: 'group',
      color: '#999',
      cursor: 'default',
      display: 'block',
      fontSize: '75%',
      fontWeight: '500',
      marginBottom: '0.25em',
      paddingLeft: spacing.baseUnit * 3,
      paddingRight: spacing.baseUnit * 3,
      textTransform: 'uppercase'
    };
  };
  var GroupHeading = function GroupHeading(props) {
    var className = props.className,
        cx = props.cx,
        getStyles = props.getStyles,
        theme = props.theme,
        selectProps = props.selectProps,
        cleanProps = _objectWithoutPropertiesLoose$1(props, ["className", "cx", "getStyles", "theme", "selectProps"]);

    return core.jsx("div", _extends$4({
      css: getStyles('groupHeading', _extends$4({
        theme: theme
      }, cleanProps)),
      className: cx({
        'group-heading': true
      }, className)
    }, cleanProps));
  };

  function _extends$5() { _extends$5 = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; }; return _extends$5.apply(this, arguments); }

  function _objectWithoutPropertiesLoose$2(source, excluded) { if (source == null) return {}; var target = {}; var sourceKeys = Object.keys(source); var key, i; for (i = 0; i < sourceKeys.length; i++) { key = sourceKeys[i]; if (excluded.indexOf(key) >= 0) continue; target[key] = source[key]; } return target; }
  var inputCSS = function inputCSS(_ref) {
    var isDisabled = _ref.isDisabled,
        _ref$theme = _ref.theme,
        spacing = _ref$theme.spacing,
        colors = _ref$theme.colors;
    return {
      margin: spacing.baseUnit / 2,
      paddingBottom: spacing.baseUnit / 2,
      paddingTop: spacing.baseUnit / 2,
      visibility: isDisabled ? 'hidden' : 'visible',
      color: colors.neutral80
    };
  };

  var inputStyle = function inputStyle(isHidden) {
    return {
      label: 'input',
      background: 0,
      border: 0,
      fontSize: 'inherit',
      opacity: isHidden ? 0 : 1,
      outline: 0,
      padding: 0,
      color: 'inherit'
    };
  };

  var Input = function Input(_ref2) {
    var className = _ref2.className,
        cx = _ref2.cx,
        getStyles = _ref2.getStyles,
        innerRef = _ref2.innerRef,
        isHidden = _ref2.isHidden,
        isDisabled = _ref2.isDisabled,
        theme = _ref2.theme,
        selectProps = _ref2.selectProps,
        props = _objectWithoutPropertiesLoose$2(_ref2, ["className", "cx", "getStyles", "innerRef", "isHidden", "isDisabled", "theme", "selectProps"]);

    return core.jsx("div", {
      css: getStyles('input', _extends$5({
        theme: theme
      }, props))
    }, core.jsx(AutosizeInput, _extends$5({
      className: cx({
        input: true
      }, className),
      inputRef: innerRef,
      inputStyle: inputStyle(isHidden),
      disabled: isDisabled
    }, props)));
  };

  function _extends$6() { _extends$6 = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; }; return _extends$6.apply(this, arguments); }
  var multiValueCSS = function multiValueCSS(_ref) {
    var _ref$theme = _ref.theme,
        spacing = _ref$theme.spacing,
        borderRadius = _ref$theme.borderRadius,
        colors = _ref$theme.colors;
    return {
      label: 'multiValue',
      backgroundColor: colors.neutral10,
      borderRadius: borderRadius / 2,
      display: 'flex',
      margin: spacing.baseUnit / 2,
      minWidth: 0 // resolves flex/text-overflow bug

    };
  };
  var multiValueLabelCSS = function multiValueLabelCSS(_ref2) {
    var _ref2$theme = _ref2.theme,
        borderRadius = _ref2$theme.borderRadius,
        colors = _ref2$theme.colors,
        cropWithEllipsis = _ref2.cropWithEllipsis;
    return {
      borderRadius: borderRadius / 2,
      color: colors.neutral80,
      fontSize: '85%',
      overflow: 'hidden',
      padding: 3,
      paddingLeft: 6,
      textOverflow: cropWithEllipsis ? 'ellipsis' : null,
      whiteSpace: 'nowrap'
    };
  };
  var multiValueRemoveCSS = function multiValueRemoveCSS(_ref3) {
    var _ref3$theme = _ref3.theme,
        spacing = _ref3$theme.spacing,
        borderRadius = _ref3$theme.borderRadius,
        colors = _ref3$theme.colors,
        isFocused = _ref3.isFocused;
    return {
      alignItems: 'center',
      borderRadius: borderRadius / 2,
      backgroundColor: isFocused && colors.dangerLight,
      display: 'flex',
      paddingLeft: spacing.baseUnit,
      paddingRight: spacing.baseUnit,
      ':hover': {
        backgroundColor: colors.dangerLight,
        color: colors.danger
      }
    };
  };
  var MultiValueGeneric = function MultiValueGeneric(_ref4) {
    var children = _ref4.children,
        innerProps = _ref4.innerProps;
    return core.jsx("div", innerProps, children);
  };
  var MultiValueContainer = MultiValueGeneric;
  var MultiValueLabel = MultiValueGeneric;
  function MultiValueRemove(_ref5) {
    var children = _ref5.children,
        innerProps = _ref5.innerProps;
    return core.jsx("div", innerProps, children || core.jsx(CrossIcon, {
      size: 14
    }));
  }

  var MultiValue = function MultiValue(props) {
    var children = props.children,
        className = props.className,
        components = props.components,
        cx = props.cx,
        data = props.data,
        getStyles = props.getStyles,
        innerProps = props.innerProps,
        isDisabled = props.isDisabled,
        removeProps = props.removeProps,
        selectProps = props.selectProps;
    var Container = components.Container,
        Label = components.Label,
        Remove = components.Remove;
    return core.jsx(core.ClassNames, null, function (_ref6) {
      var css = _ref6.css,
          emotionCx = _ref6.cx;
      return core.jsx(Container, {
        data: data,
        innerProps: _extends$6({}, innerProps, {
          className: emotionCx(css(getStyles('multiValue', props)), cx({
            'multi-value': true,
            'multi-value--is-disabled': isDisabled
          }, className))
        }),
        selectProps: selectProps
      }, core.jsx(Label, {
        data: data,
        innerProps: {
          className: emotionCx(css(getStyles('multiValueLabel', props)), cx({
            'multi-value__label': true
          }, className))
        },
        selectProps: selectProps
      }, children), core.jsx(Remove, {
        data: data,
        innerProps: _extends$6({
          className: emotionCx(css(getStyles('multiValueRemove', props)), cx({
            'multi-value__remove': true
          }, className))
        }, removeProps),
        selectProps: selectProps
      }));
    });
  };

  MultiValue.defaultProps = {
    cropWithEllipsis: true
  };

  function _extends$7() { _extends$7 = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; }; return _extends$7.apply(this, arguments); }
  var optionCSS = function optionCSS(_ref) {
    var isDisabled = _ref.isDisabled,
        isFocused = _ref.isFocused,
        isSelected = _ref.isSelected,
        _ref$theme = _ref.theme,
        spacing = _ref$theme.spacing,
        colors = _ref$theme.colors;
    return {
      label: 'option',
      backgroundColor: isSelected ? colors.primary : isFocused ? colors.primary25 : 'transparent',
      color: isDisabled ? colors.neutral20 : isSelected ? colors.neutral0 : 'inherit',
      cursor: 'default',
      display: 'block',
      fontSize: 'inherit',
      padding: spacing.baseUnit * 2 + "px " + spacing.baseUnit * 3 + "px",
      width: '100%',
      userSelect: 'none',
      WebkitTapHighlightColor: 'rgba(0, 0, 0, 0)',
      // provide some affordance on touch devices
      ':active': {
        backgroundColor: !isDisabled && (isSelected ? colors.primary : colors.primary50)
      }
    };
  };

  var Option = function Option(props) {
    var children = props.children,
        className = props.className,
        cx = props.cx,
        getStyles = props.getStyles,
        isDisabled = props.isDisabled,
        isFocused = props.isFocused,
        isSelected = props.isSelected,
        innerRef = props.innerRef,
        innerProps = props.innerProps;
    return core.jsx("div", _extends$7({
      css: getStyles('option', props),
      className: cx({
        option: true,
        'option--is-disabled': isDisabled,
        'option--is-focused': isFocused,
        'option--is-selected': isSelected
      }, className),
      ref: innerRef
    }, innerProps), children);
  };

  function _extends$8() { _extends$8 = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; }; return _extends$8.apply(this, arguments); }
  var placeholderCSS = function placeholderCSS(_ref) {
    var _ref$theme = _ref.theme,
        spacing = _ref$theme.spacing,
        colors = _ref$theme.colors;
    return {
      label: 'placeholder',
      color: colors.neutral50,
      marginLeft: spacing.baseUnit / 2,
      marginRight: spacing.baseUnit / 2,
      position: 'absolute',
      top: '50%',
      transform: 'translateY(-50%)'
    };
  };

  var Placeholder = function Placeholder(props) {
    var children = props.children,
        className = props.className,
        cx = props.cx,
        getStyles = props.getStyles,
        innerProps = props.innerProps;
    return core.jsx("div", _extends$8({
      css: getStyles('placeholder', props),
      className: cx({
        placeholder: true
      }, className)
    }, innerProps), children);
  };

  function _extends$9() { _extends$9 = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; }; return _extends$9.apply(this, arguments); }
  var css$1$1 = function css(_ref) {
    var isDisabled = _ref.isDisabled,
        _ref$theme = _ref.theme,
        spacing = _ref$theme.spacing,
        colors = _ref$theme.colors;
    return {
      label: 'singleValue',
      color: isDisabled ? colors.neutral40 : colors.neutral80,
      marginLeft: spacing.baseUnit / 2,
      marginRight: spacing.baseUnit / 2,
      maxWidth: "calc(100% - " + spacing.baseUnit * 2 + "px)",
      overflow: 'hidden',
      position: 'absolute',
      textOverflow: 'ellipsis',
      whiteSpace: 'nowrap',
      top: '50%',
      transform: 'translateY(-50%)'
    };
  };

  var SingleValue = function SingleValue(props) {
    var children = props.children,
        className = props.className,
        cx = props.cx,
        getStyles = props.getStyles,
        isDisabled = props.isDisabled,
        innerProps = props.innerProps;
    return core.jsx("div", _extends$9({
      css: getStyles('singleValue', props),
      className: cx({
        'single-value': true,
        'single-value--is-disabled': isDisabled
      }, className)
    }, innerProps), children);
  };

  function _extends$a() { _extends$a = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; }; return _extends$a.apply(this, arguments); }
  var components = {
    ClearIndicator: ClearIndicator,
    Control: Control,
    DropdownIndicator: DropdownIndicator,
    DownChevron: DownChevron,
    CrossIcon: CrossIcon,
    Group: Group,
    GroupHeading: GroupHeading,
    IndicatorsContainer: IndicatorsContainer,
    IndicatorSeparator: IndicatorSeparator,
    Input: Input,
    LoadingIndicator: LoadingIndicator,
    Menu: Menu,
    MenuList: MenuList,
    MenuPortal: MenuPortal,
    LoadingMessage: LoadingMessage,
    NoOptionsMessage: NoOptionsMessage,
    MultiValue: MultiValue,
    MultiValueContainer: MultiValueContainer,
    MultiValueLabel: MultiValueLabel,
    MultiValueRemove: MultiValueRemove,
    Option: Option,
    Placeholder: Placeholder,
    SelectContainer: SelectContainer,
    SingleValue: SingleValue,
    ValueContainer: ValueContainer
  };
  var defaultComponents = function defaultComponents(props) {
    return _extends$a({}, components, props.components);
  };

  var diacritics = [{
    base: 'A',
    letters: /[\u0041\u24B6\uFF21\u00C0\u00C1\u00C2\u1EA6\u1EA4\u1EAA\u1EA8\u00C3\u0100\u0102\u1EB0\u1EAE\u1EB4\u1EB2\u0226\u01E0\u00C4\u01DE\u1EA2\u00C5\u01FA\u01CD\u0200\u0202\u1EA0\u1EAC\u1EB6\u1E00\u0104\u023A\u2C6F]/g
  }, {
    base: 'AA',
    letters: /[\uA732]/g
  }, {
    base: 'AE',
    letters: /[\u00C6\u01FC\u01E2]/g
  }, {
    base: 'AO',
    letters: /[\uA734]/g
  }, {
    base: 'AU',
    letters: /[\uA736]/g
  }, {
    base: 'AV',
    letters: /[\uA738\uA73A]/g
  }, {
    base: 'AY',
    letters: /[\uA73C]/g
  }, {
    base: 'B',
    letters: /[\u0042\u24B7\uFF22\u1E02\u1E04\u1E06\u0243\u0182\u0181]/g
  }, {
    base: 'C',
    letters: /[\u0043\u24B8\uFF23\u0106\u0108\u010A\u010C\u00C7\u1E08\u0187\u023B\uA73E]/g
  }, {
    base: 'D',
    letters: /[\u0044\u24B9\uFF24\u1E0A\u010E\u1E0C\u1E10\u1E12\u1E0E\u0110\u018B\u018A\u0189\uA779]/g
  }, {
    base: 'DZ',
    letters: /[\u01F1\u01C4]/g
  }, {
    base: 'Dz',
    letters: /[\u01F2\u01C5]/g
  }, {
    base: 'E',
    letters: /[\u0045\u24BA\uFF25\u00C8\u00C9\u00CA\u1EC0\u1EBE\u1EC4\u1EC2\u1EBC\u0112\u1E14\u1E16\u0114\u0116\u00CB\u1EBA\u011A\u0204\u0206\u1EB8\u1EC6\u0228\u1E1C\u0118\u1E18\u1E1A\u0190\u018E]/g
  }, {
    base: 'F',
    letters: /[\u0046\u24BB\uFF26\u1E1E\u0191\uA77B]/g
  }, {
    base: 'G',
    letters: /[\u0047\u24BC\uFF27\u01F4\u011C\u1E20\u011E\u0120\u01E6\u0122\u01E4\u0193\uA7A0\uA77D\uA77E]/g
  }, {
    base: 'H',
    letters: /[\u0048\u24BD\uFF28\u0124\u1E22\u1E26\u021E\u1E24\u1E28\u1E2A\u0126\u2C67\u2C75\uA78D]/g
  }, {
    base: 'I',
    letters: /[\u0049\u24BE\uFF29\u00CC\u00CD\u00CE\u0128\u012A\u012C\u0130\u00CF\u1E2E\u1EC8\u01CF\u0208\u020A\u1ECA\u012E\u1E2C\u0197]/g
  }, {
    base: 'J',
    letters: /[\u004A\u24BF\uFF2A\u0134\u0248]/g
  }, {
    base: 'K',
    letters: /[\u004B\u24C0\uFF2B\u1E30\u01E8\u1E32\u0136\u1E34\u0198\u2C69\uA740\uA742\uA744\uA7A2]/g
  }, {
    base: 'L',
    letters: /[\u004C\u24C1\uFF2C\u013F\u0139\u013D\u1E36\u1E38\u013B\u1E3C\u1E3A\u0141\u023D\u2C62\u2C60\uA748\uA746\uA780]/g
  }, {
    base: 'LJ',
    letters: /[\u01C7]/g
  }, {
    base: 'Lj',
    letters: /[\u01C8]/g
  }, {
    base: 'M',
    letters: /[\u004D\u24C2\uFF2D\u1E3E\u1E40\u1E42\u2C6E\u019C]/g
  }, {
    base: 'N',
    letters: /[\u004E\u24C3\uFF2E\u01F8\u0143\u00D1\u1E44\u0147\u1E46\u0145\u1E4A\u1E48\u0220\u019D\uA790\uA7A4]/g
  }, {
    base: 'NJ',
    letters: /[\u01CA]/g
  }, {
    base: 'Nj',
    letters: /[\u01CB]/g
  }, {
    base: 'O',
    letters: /[\u004F\u24C4\uFF2F\u00D2\u00D3\u00D4\u1ED2\u1ED0\u1ED6\u1ED4\u00D5\u1E4C\u022C\u1E4E\u014C\u1E50\u1E52\u014E\u022E\u0230\u00D6\u022A\u1ECE\u0150\u01D1\u020C\u020E\u01A0\u1EDC\u1EDA\u1EE0\u1EDE\u1EE2\u1ECC\u1ED8\u01EA\u01EC\u00D8\u01FE\u0186\u019F\uA74A\uA74C]/g
  }, {
    base: 'OI',
    letters: /[\u01A2]/g
  }, {
    base: 'OO',
    letters: /[\uA74E]/g
  }, {
    base: 'OU',
    letters: /[\u0222]/g
  }, {
    base: 'P',
    letters: /[\u0050\u24C5\uFF30\u1E54\u1E56\u01A4\u2C63\uA750\uA752\uA754]/g
  }, {
    base: 'Q',
    letters: /[\u0051\u24C6\uFF31\uA756\uA758\u024A]/g
  }, {
    base: 'R',
    letters: /[\u0052\u24C7\uFF32\u0154\u1E58\u0158\u0210\u0212\u1E5A\u1E5C\u0156\u1E5E\u024C\u2C64\uA75A\uA7A6\uA782]/g
  }, {
    base: 'S',
    letters: /[\u0053\u24C8\uFF33\u1E9E\u015A\u1E64\u015C\u1E60\u0160\u1E66\u1E62\u1E68\u0218\u015E\u2C7E\uA7A8\uA784]/g
  }, {
    base: 'T',
    letters: /[\u0054\u24C9\uFF34\u1E6A\u0164\u1E6C\u021A\u0162\u1E70\u1E6E\u0166\u01AC\u01AE\u023E\uA786]/g
  }, {
    base: 'TZ',
    letters: /[\uA728]/g
  }, {
    base: 'U',
    letters: /[\u0055\u24CA\uFF35\u00D9\u00DA\u00DB\u0168\u1E78\u016A\u1E7A\u016C\u00DC\u01DB\u01D7\u01D5\u01D9\u1EE6\u016E\u0170\u01D3\u0214\u0216\u01AF\u1EEA\u1EE8\u1EEE\u1EEC\u1EF0\u1EE4\u1E72\u0172\u1E76\u1E74\u0244]/g
  }, {
    base: 'V',
    letters: /[\u0056\u24CB\uFF36\u1E7C\u1E7E\u01B2\uA75E\u0245]/g
  }, {
    base: 'VY',
    letters: /[\uA760]/g
  }, {
    base: 'W',
    letters: /[\u0057\u24CC\uFF37\u1E80\u1E82\u0174\u1E86\u1E84\u1E88\u2C72]/g
  }, {
    base: 'X',
    letters: /[\u0058\u24CD\uFF38\u1E8A\u1E8C]/g
  }, {
    base: 'Y',
    letters: /[\u0059\u24CE\uFF39\u1EF2\u00DD\u0176\u1EF8\u0232\u1E8E\u0178\u1EF6\u1EF4\u01B3\u024E\u1EFE]/g
  }, {
    base: 'Z',
    letters: /[\u005A\u24CF\uFF3A\u0179\u1E90\u017B\u017D\u1E92\u1E94\u01B5\u0224\u2C7F\u2C6B\uA762]/g
  }, {
    base: 'a',
    letters: /[\u0061\u24D0\uFF41\u1E9A\u00E0\u00E1\u00E2\u1EA7\u1EA5\u1EAB\u1EA9\u00E3\u0101\u0103\u1EB1\u1EAF\u1EB5\u1EB3\u0227\u01E1\u00E4\u01DF\u1EA3\u00E5\u01FB\u01CE\u0201\u0203\u1EA1\u1EAD\u1EB7\u1E01\u0105\u2C65\u0250]/g
  }, {
    base: 'aa',
    letters: /[\uA733]/g
  }, {
    base: 'ae',
    letters: /[\u00E6\u01FD\u01E3]/g
  }, {
    base: 'ao',
    letters: /[\uA735]/g
  }, {
    base: 'au',
    letters: /[\uA737]/g
  }, {
    base: 'av',
    letters: /[\uA739\uA73B]/g
  }, {
    base: 'ay',
    letters: /[\uA73D]/g
  }, {
    base: 'b',
    letters: /[\u0062\u24D1\uFF42\u1E03\u1E05\u1E07\u0180\u0183\u0253]/g
  }, {
    base: 'c',
    letters: /[\u0063\u24D2\uFF43\u0107\u0109\u010B\u010D\u00E7\u1E09\u0188\u023C\uA73F\u2184]/g
  }, {
    base: 'd',
    letters: /[\u0064\u24D3\uFF44\u1E0B\u010F\u1E0D\u1E11\u1E13\u1E0F\u0111\u018C\u0256\u0257\uA77A]/g
  }, {
    base: 'dz',
    letters: /[\u01F3\u01C6]/g
  }, {
    base: 'e',
    letters: /[\u0065\u24D4\uFF45\u00E8\u00E9\u00EA\u1EC1\u1EBF\u1EC5\u1EC3\u1EBD\u0113\u1E15\u1E17\u0115\u0117\u00EB\u1EBB\u011B\u0205\u0207\u1EB9\u1EC7\u0229\u1E1D\u0119\u1E19\u1E1B\u0247\u025B\u01DD]/g
  }, {
    base: 'f',
    letters: /[\u0066\u24D5\uFF46\u1E1F\u0192\uA77C]/g
  }, {
    base: 'g',
    letters: /[\u0067\u24D6\uFF47\u01F5\u011D\u1E21\u011F\u0121\u01E7\u0123\u01E5\u0260\uA7A1\u1D79\uA77F]/g
  }, {
    base: 'h',
    letters: /[\u0068\u24D7\uFF48\u0125\u1E23\u1E27\u021F\u1E25\u1E29\u1E2B\u1E96\u0127\u2C68\u2C76\u0265]/g
  }, {
    base: 'hv',
    letters: /[\u0195]/g
  }, {
    base: 'i',
    letters: /[\u0069\u24D8\uFF49\u00EC\u00ED\u00EE\u0129\u012B\u012D\u00EF\u1E2F\u1EC9\u01D0\u0209\u020B\u1ECB\u012F\u1E2D\u0268\u0131]/g
  }, {
    base: 'j',
    letters: /[\u006A\u24D9\uFF4A\u0135\u01F0\u0249]/g
  }, {
    base: 'k',
    letters: /[\u006B\u24DA\uFF4B\u1E31\u01E9\u1E33\u0137\u1E35\u0199\u2C6A\uA741\uA743\uA745\uA7A3]/g
  }, {
    base: 'l',
    letters: /[\u006C\u24DB\uFF4C\u0140\u013A\u013E\u1E37\u1E39\u013C\u1E3D\u1E3B\u017F\u0142\u019A\u026B\u2C61\uA749\uA781\uA747]/g
  }, {
    base: 'lj',
    letters: /[\u01C9]/g
  }, {
    base: 'm',
    letters: /[\u006D\u24DC\uFF4D\u1E3F\u1E41\u1E43\u0271\u026F]/g
  }, {
    base: 'n',
    letters: /[\u006E\u24DD\uFF4E\u01F9\u0144\u00F1\u1E45\u0148\u1E47\u0146\u1E4B\u1E49\u019E\u0272\u0149\uA791\uA7A5]/g
  }, {
    base: 'nj',
    letters: /[\u01CC]/g
  }, {
    base: 'o',
    letters: /[\u006F\u24DE\uFF4F\u00F2\u00F3\u00F4\u1ED3\u1ED1\u1ED7\u1ED5\u00F5\u1E4D\u022D\u1E4F\u014D\u1E51\u1E53\u014F\u022F\u0231\u00F6\u022B\u1ECF\u0151\u01D2\u020D\u020F\u01A1\u1EDD\u1EDB\u1EE1\u1EDF\u1EE3\u1ECD\u1ED9\u01EB\u01ED\u00F8\u01FF\u0254\uA74B\uA74D\u0275]/g
  }, {
    base: 'oi',
    letters: /[\u01A3]/g
  }, {
    base: 'ou',
    letters: /[\u0223]/g
  }, {
    base: 'oo',
    letters: /[\uA74F]/g
  }, {
    base: 'p',
    letters: /[\u0070\u24DF\uFF50\u1E55\u1E57\u01A5\u1D7D\uA751\uA753\uA755]/g
  }, {
    base: 'q',
    letters: /[\u0071\u24E0\uFF51\u024B\uA757\uA759]/g
  }, {
    base: 'r',
    letters: /[\u0072\u24E1\uFF52\u0155\u1E59\u0159\u0211\u0213\u1E5B\u1E5D\u0157\u1E5F\u024D\u027D\uA75B\uA7A7\uA783]/g
  }, {
    base: 's',
    letters: /[\u0073\u24E2\uFF53\u00DF\u015B\u1E65\u015D\u1E61\u0161\u1E67\u1E63\u1E69\u0219\u015F\u023F\uA7A9\uA785\u1E9B]/g
  }, {
    base: 't',
    letters: /[\u0074\u24E3\uFF54\u1E6B\u1E97\u0165\u1E6D\u021B\u0163\u1E71\u1E6F\u0167\u01AD\u0288\u2C66\uA787]/g
  }, {
    base: 'tz',
    letters: /[\uA729]/g
  }, {
    base: 'u',
    letters: /[\u0075\u24E4\uFF55\u00F9\u00FA\u00FB\u0169\u1E79\u016B\u1E7B\u016D\u00FC\u01DC\u01D8\u01D6\u01DA\u1EE7\u016F\u0171\u01D4\u0215\u0217\u01B0\u1EEB\u1EE9\u1EEF\u1EED\u1EF1\u1EE5\u1E73\u0173\u1E77\u1E75\u0289]/g
  }, {
    base: 'v',
    letters: /[\u0076\u24E5\uFF56\u1E7D\u1E7F\u028B\uA75F\u028C]/g
  }, {
    base: 'vy',
    letters: /[\uA761]/g
  }, {
    base: 'w',
    letters: /[\u0077\u24E6\uFF57\u1E81\u1E83\u0175\u1E87\u1E85\u1E98\u1E89\u2C73]/g
  }, {
    base: 'x',
    letters: /[\u0078\u24E7\uFF58\u1E8B\u1E8D]/g
  }, {
    base: 'y',
    letters: /[\u0079\u24E8\uFF59\u1EF3\u00FD\u0177\u1EF9\u0233\u1E8F\u00FF\u1EF7\u1E99\u1EF5\u01B4\u024F\u1EFF]/g
  }, {
    base: 'z',
    letters: /[\u007A\u24E9\uFF5A\u017A\u1E91\u017C\u017E\u1E93\u1E95\u01B6\u0225\u0240\u2C6C\uA763]/g
  }];
  var stripDiacritics = function stripDiacritics(str) {
    for (var i = 0; i < diacritics.length; i++) {
      str = str.replace(diacritics[i].letters, diacritics[i].base);
    }

    return str;
  };

  function _extends$b() { _extends$b = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; }; return _extends$b.apply(this, arguments); }

  var trimString = function trimString(str) {
    return str.replace(/^\s+|\s+$/g, '');
  };

  var defaultStringify = function defaultStringify(option) {
    return option.label + " " + option.value;
  };

  var createFilter = function createFilter(config) {
    return function (option, rawInput) {
      var _ignoreCase$ignoreAcc = _extends$b({
        ignoreCase: true,
        ignoreAccents: true,
        stringify: defaultStringify,
        trim: true,
        matchFrom: 'any'
      }, config),
          ignoreCase = _ignoreCase$ignoreAcc.ignoreCase,
          ignoreAccents = _ignoreCase$ignoreAcc.ignoreAccents,
          stringify = _ignoreCase$ignoreAcc.stringify,
          trim = _ignoreCase$ignoreAcc.trim,
          matchFrom = _ignoreCase$ignoreAcc.matchFrom;

      var input = trim ? trimString(rawInput) : rawInput;
      var candidate = trim ? trimString(stringify(option)) : stringify(option);

      if (ignoreCase) {
        input = input.toLowerCase();
        candidate = candidate.toLowerCase();
      }

      if (ignoreAccents) {
        input = stripDiacritics(input);
        candidate = stripDiacritics(candidate);
      }

      return matchFrom === 'start' ? candidate.substr(0, input.length) === input : candidate.indexOf(input) > -1;
    };
  };

  function _extends$1$2() { _extends$1$2 = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; }; return _extends$1$2.apply(this, arguments); }

  var _ref = process.env.NODE_ENV === "production" ? {
    name: "1laao21-a11yText",
    styles: "label:a11yText;z-index:9999;border:0;clip:rect(1px, 1px, 1px, 1px);height:1px;width:1px;position:absolute;overflow:hidden;padding:0;white-space:nowrap;"
  } : {
    name: "1laao21-a11yText",
    styles: "label:a11yText;z-index:9999;border:0;clip:rect(1px, 1px, 1px, 1px);height:1px;width:1px;position:absolute;overflow:hidden;padding:0;white-space:nowrap;",
    map: "/*# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbIkExMXlUZXh0LmpzIl0sIm5hbWVzIjpbXSwibWFwcGluZ3MiOiJBQVFNIiwiZmlsZSI6IkExMXlUZXh0LmpzIiwic291cmNlc0NvbnRlbnQiOlsiLy8gQGZsb3dcbi8qKiBAanN4IGpzeCAqL1xuaW1wb3J0IHsgdHlwZSBFbGVtZW50Q29uZmlnIH0gZnJvbSAncmVhY3QnO1xuaW1wb3J0IHsganN4IH0gZnJvbSAnQGVtb3Rpb24vY29yZSc7XG5cbi8vIEFzc2lzdGl2ZSB0ZXh0IHRvIGRlc2NyaWJlIHZpc3VhbCBlbGVtZW50cy4gSGlkZGVuIGZvciBzaWdodGVkIHVzZXJzLlxuY29uc3QgQTExeVRleHQgPSAocHJvcHM6IEVsZW1lbnRDb25maWc8J3NwYW4nPikgPT4gKFxuICAgIDxzcGFuXG4gICAgICBjc3M9e3tcbiAgICAgICAgbGFiZWw6ICdhMTF5VGV4dCcsXG4gICAgICAgIHpJbmRleDogOTk5OSxcbiAgICAgICAgYm9yZGVyOiAwLFxuICAgICAgICBjbGlwOiAncmVjdCgxcHgsIDFweCwgMXB4LCAxcHgpJyxcbiAgICAgICAgaGVpZ2h0OiAxLFxuICAgICAgICB3aWR0aDogMSxcbiAgICAgICAgcG9zaXRpb246ICdhYnNvbHV0ZScsXG4gICAgICAgIG92ZXJmbG93OiAnaGlkZGVuJyxcbiAgICAgICAgcGFkZGluZzogMCxcbiAgICAgICAgd2hpdGVTcGFjZTogJ25vd3JhcCcsXG4gICAgICB9fVxuICAgICAgey4uLnByb3BzfVxuICAgIC8+XG4pO1xuXG5leHBvcnQgZGVmYXVsdCBBMTF5VGV4dDtcbiJdfQ== */"
  };

  var A11yText = function A11yText(props) {
    return core.jsx("span", _extends$1$2({
      css: _ref
    }, props));
  };

  function _extends$2$1() { _extends$2$1 = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; }; return _extends$2$1.apply(this, arguments); }

  function _objectWithoutPropertiesLoose$3(source, excluded) { if (source == null) return {}; var target = {}; var sourceKeys = Object.keys(source); var key, i; for (i = 0; i < sourceKeys.length; i++) { key = sourceKeys[i]; if (excluded.indexOf(key) >= 0) continue; target[key] = source[key]; } return target; }
  function DummyInput(_ref) {
    var inProp = _ref.in,
        out = _ref.out,
        onExited = _ref.onExited,
        appear = _ref.appear,
        enter = _ref.enter,
        exit = _ref.exit,
        innerRef = _ref.innerRef,
        emotion = _ref.emotion,
        props = _objectWithoutPropertiesLoose$3(_ref, ["in", "out", "onExited", "appear", "enter", "exit", "innerRef", "emotion"]);

    return core.jsx("input", _extends$2$1({
      ref: innerRef
    }, props, {
      css:
      /*#__PURE__*/
      css({
        label: 'dummyInput',
        // get rid of any default styles
        background: 0,
        border: 0,
        fontSize: 'inherit',
        outline: 0,
        padding: 0,
        // important! without `width` browsers won't allow focus
        width: 1,
        // remove cursor on desktop
        color: 'transparent',
        // remove cursor on mobile whilst maintaining "scroll into view" behaviour
        left: -100,
        opacity: 0,
        position: 'relative',
        transform: 'scale(0)'
      }, process.env.NODE_ENV === "production" ? "" : "/*# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbIkR1bW15SW5wdXQuanMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBbUJNIiwiZmlsZSI6IkR1bW15SW5wdXQuanMiLCJzb3VyY2VzQ29udGVudCI6WyIvLyBAZmxvd1xuLyoqIEBqc3gganN4ICovXG5pbXBvcnQgeyBqc3ggfSBmcm9tICdAZW1vdGlvbi9jb3JlJztcblxuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24gRHVtbXlJbnB1dCh7XG4gIGluOiBpblByb3AsXG4gIG91dCxcbiAgb25FeGl0ZWQsXG4gIGFwcGVhcixcbiAgZW50ZXIsXG4gIGV4aXQsXG4gIGlubmVyUmVmLFxuICBlbW90aW9uLFxuICAuLi5wcm9wc1xufTogYW55KSB7XG4gIHJldHVybiAoXG4gICAgPGlucHV0XG4gICAgICByZWY9e2lubmVyUmVmfVxuICAgICAgey4uLnByb3BzfVxuICAgICAgY3NzPXt7XG4gICAgICAgIGxhYmVsOiAnZHVtbXlJbnB1dCcsXG4gICAgICAgIC8vIGdldCByaWQgb2YgYW55IGRlZmF1bHQgc3R5bGVzXG4gICAgICAgIGJhY2tncm91bmQ6IDAsXG4gICAgICAgIGJvcmRlcjogMCxcbiAgICAgICAgZm9udFNpemU6ICdpbmhlcml0JyxcbiAgICAgICAgb3V0bGluZTogMCxcbiAgICAgICAgcGFkZGluZzogMCxcbiAgICAgICAgLy8gaW1wb3J0YW50ISB3aXRob3V0IGB3aWR0aGAgYnJvd3NlcnMgd29uJ3QgYWxsb3cgZm9jdXNcbiAgICAgICAgd2lkdGg6IDEsXG5cbiAgICAgICAgLy8gcmVtb3ZlIGN1cnNvciBvbiBkZXNrdG9wXG4gICAgICAgIGNvbG9yOiAndHJhbnNwYXJlbnQnLFxuXG4gICAgICAgIC8vIHJlbW92ZSBjdXJzb3Igb24gbW9iaWxlIHdoaWxzdCBtYWludGFpbmluZyBcInNjcm9sbCBpbnRvIHZpZXdcIiBiZWhhdmlvdXJcbiAgICAgICAgbGVmdDogLTEwMCxcbiAgICAgICAgb3BhY2l0eTogMCxcbiAgICAgICAgcG9zaXRpb246ICdyZWxhdGl2ZScsXG4gICAgICAgIHRyYW5zZm9ybTogJ3NjYWxlKDApJyxcbiAgICAgIH19XG4gICAgLz5cbiAgKTtcbn1cbiJdfQ== */")
    }));
  }

  function _inheritsLoose$1(subClass, superClass) { subClass.prototype = Object.create(superClass.prototype); subClass.prototype.constructor = subClass; subClass.__proto__ = superClass; }

  var NodeResolver =
  /*#__PURE__*/
  function (_Component) {
    _inheritsLoose$1(NodeResolver, _Component);

    function NodeResolver() {
      return _Component.apply(this, arguments) || this;
    }

    var _proto = NodeResolver.prototype;

    _proto.componentDidMount = function componentDidMount() {
      this.props.innerRef(reactDom.findDOMNode(this));
    };

    _proto.componentWillUnmount = function componentWillUnmount() {
      this.props.innerRef(null);
    };

    _proto.render = function render() {
      return this.props.children;
    };

    return NodeResolver;
  }(React.Component);

  var STYLE_KEYS = ['boxSizing', 'height', 'overflow', 'paddingRight', 'position'];
  var LOCK_STYLES = {
    boxSizing: 'border-box',
    // account for possible declaration `width: 100%;` on body
    overflow: 'hidden',
    position: 'relative',
    height: '100%'
  };

  function preventTouchMove(e) {
    e.preventDefault();
  }
  function allowTouchMove(e) {
    e.stopPropagation();
  }
  function preventInertiaScroll() {
    var top = this.scrollTop;
    var totalScroll = this.scrollHeight;
    var currentScroll = top + this.offsetHeight;

    if (top === 0) {
      this.scrollTop = 1;
    } else if (currentScroll === totalScroll) {
      this.scrollTop = top - 1;
    }
  } // `ontouchstart` check works on most browsers
  // `maxTouchPoints` works on IE10/11 and Surface

  function isTouchDevice() {
    return 'ontouchstart' in window || navigator.maxTouchPoints;
  }

  function _inheritsLoose$1$1(subClass, superClass) { subClass.prototype = Object.create(superClass.prototype); subClass.prototype.constructor = subClass; subClass.__proto__ = superClass; }
  var canUseDOM = !!(typeof window !== 'undefined' && window.document && window.document.createElement);
  var activeScrollLocks = 0;

  var ScrollLock =
  /*#__PURE__*/
  function (_Component) {
    _inheritsLoose$1$1(ScrollLock, _Component);

    function ScrollLock() {
      var _this;

      for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
        args[_key] = arguments[_key];
      }

      _this = _Component.call.apply(_Component, [this].concat(args)) || this;
      _this.originalStyles = {};
      _this.listenerOptions = {
        capture: false,
        passive: false
      };
      return _this;
    }

    var _proto = ScrollLock.prototype;

    _proto.componentDidMount = function componentDidMount() {
      var _this2 = this;

      if (!canUseDOM) return;
      var _this$props = this.props,
          accountForScrollbars = _this$props.accountForScrollbars,
          touchScrollTarget = _this$props.touchScrollTarget;
      var target = document.body;
      var targetStyle = target && target.style;

      if (accountForScrollbars) {
        // store any styles already applied to the body
        STYLE_KEYS.forEach(function (key) {
          var val = targetStyle && targetStyle[key];
          _this2.originalStyles[key] = val;
        });
      } // apply the lock styles and padding if this is the first scroll lock


      if (accountForScrollbars && activeScrollLocks < 1) {
        var currentPadding = parseInt(this.originalStyles.paddingRight, 10) || 0;
        var clientWidth = document.body ? document.body.clientWidth : 0;
        var adjustedPadding = window.innerWidth - clientWidth + currentPadding || 0;
        Object.keys(LOCK_STYLES).forEach(function (key) {
          var val = LOCK_STYLES[key];

          if (targetStyle) {
            targetStyle[key] = val;
          }
        });

        if (targetStyle) {
          targetStyle.paddingRight = adjustedPadding + "px";
        }
      } // account for touch devices


      if (target && isTouchDevice()) {
        // Mobile Safari ignores { overflow: hidden } declaration on the body.
        target.addEventListener('touchmove', preventTouchMove, this.listenerOptions); // Allow scroll on provided target

        if (touchScrollTarget) {
          touchScrollTarget.addEventListener('touchstart', preventInertiaScroll, this.listenerOptions);
          touchScrollTarget.addEventListener('touchmove', allowTouchMove, this.listenerOptions);
        }
      } // increment active scroll locks


      activeScrollLocks += 1;
    };

    _proto.componentWillUnmount = function componentWillUnmount() {
      var _this3 = this;

      if (!canUseDOM) return;
      var _this$props2 = this.props,
          accountForScrollbars = _this$props2.accountForScrollbars,
          touchScrollTarget = _this$props2.touchScrollTarget;
      var target = document.body;
      var targetStyle = target && target.style; // safely decrement active scroll locks

      activeScrollLocks = Math.max(activeScrollLocks - 1, 0); // reapply original body styles, if any

      if (accountForScrollbars && activeScrollLocks < 1) {
        STYLE_KEYS.forEach(function (key) {
          var val = _this3.originalStyles[key];

          if (targetStyle) {
            targetStyle[key] = val;
          }
        });
      } // remove touch listeners


      if (target && isTouchDevice()) {
        target.removeEventListener('touchmove', preventTouchMove, this.listenerOptions);

        if (touchScrollTarget) {
          touchScrollTarget.removeEventListener('touchstart', preventInertiaScroll, this.listenerOptions);
          touchScrollTarget.removeEventListener('touchmove', allowTouchMove, this.listenerOptions);
        }
      }
    };

    _proto.render = function render() {
      return null;
    };

    return ScrollLock;
  }(React.Component);

  ScrollLock.defaultProps = {
    accountForScrollbars: true
  };

  function _inheritsLoose$2(subClass, superClass) { subClass.prototype = Object.create(superClass.prototype); subClass.prototype.constructor = subClass; subClass.__proto__ = superClass; }

  var _ref$1 = process.env.NODE_ENV === "production" ? {
    name: "1dsbpcp",
    styles: "position:fixed;left:0;bottom:0;right:0;top:0;"
  } : {
    name: "1dsbpcp",
    styles: "position:fixed;left:0;bottom:0;right:0;top:0;",
    map: "/*# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbIlNjcm9sbEJsb2NrLmpzIl0sIm5hbWVzIjpbXSwibWFwcGluZ3MiOiJBQTZEVSIsImZpbGUiOiJTY3JvbGxCbG9jay5qcyIsInNvdXJjZXNDb250ZW50IjpbIi8vIEBmbG93XG4vKiogQGpzeCBqc3ggKi9cbmltcG9ydCB7IFB1cmVDb21wb25lbnQsIHR5cGUgRWxlbWVudCB9IGZyb20gJ3JlYWN0JztcbmltcG9ydCB7IGpzeCB9IGZyb20gJ0BlbW90aW9uL2NvcmUnO1xuaW1wb3J0IE5vZGVSZXNvbHZlciBmcm9tICcuL05vZGVSZXNvbHZlcic7XG5pbXBvcnQgU2Nyb2xsTG9jayBmcm9tICcuL1Njcm9sbExvY2svaW5kZXgnO1xuXG50eXBlIFByb3BzID0ge1xuICBjaGlsZHJlbjogRWxlbWVudDwqPixcbiAgaXNFbmFibGVkOiBib29sZWFuLFxufTtcbnR5cGUgU3RhdGUgPSB7XG4gIHRvdWNoU2Nyb2xsVGFyZ2V0OiBIVE1MRWxlbWVudCB8IG51bGwsXG59O1xuXG4vLyBOT1RFOlxuLy8gV2Ugc2hvdWxkbid0IG5lZWQgdGhpcyBhZnRlciB1cGRhdGluZyB0byBSZWFjdCB2MTYuMy4wLCB3aGljaCBpbnRyb2R1Y2VzOlxuLy8gLSBjcmVhdGVSZWYoKSBodHRwczovL3JlYWN0anMub3JnL2RvY3MvcmVhY3QtYXBpLmh0bWwjcmVhY3RjcmVhdGVyZWZcbi8vIC0gZm9yd2FyZFJlZigpIGh0dHBzOi8vcmVhY3Rqcy5vcmcvZG9jcy9yZWFjdC1hcGkuaHRtbCNyZWFjdGZvcndhcmRyZWZcblxuZXhwb3J0IGRlZmF1bHQgY2xhc3MgU2Nyb2xsQmxvY2sgZXh0ZW5kcyBQdXJlQ29tcG9uZW50PFByb3BzLCBTdGF0ZT4ge1xuICBzdGF0ZSA9IHsgdG91Y2hTY3JvbGxUYXJnZXQ6IG51bGwgfTtcblxuICAvLyBtdXN0IGJlIGluIHN0YXRlIHRvIHRyaWdnZXIgYSByZS1yZW5kZXIsIG9ubHkgcnVucyBvbmNlIHBlciBpbnN0YW5jZVxuICBnZXRTY3JvbGxUYXJnZXQgPSAocmVmOiBIVE1MRWxlbWVudCkgPT4ge1xuICAgIGlmIChyZWYgPT09IHRoaXMuc3RhdGUudG91Y2hTY3JvbGxUYXJnZXQpIHJldHVybjtcbiAgICB0aGlzLnNldFN0YXRlKHsgdG91Y2hTY3JvbGxUYXJnZXQ6IHJlZiB9KTtcbiAgfTtcblxuICAvLyB0aGlzIHdpbGwgY2xvc2UgdGhlIG1lbnUgd2hlbiBhIHVzZXIgY2xpY2tzIG91dHNpZGVcbiAgYmx1clNlbGVjdElucHV0ID0gKCkgPT4ge1xuICAgIGlmIChkb2N1bWVudC5hY3RpdmVFbGVtZW50KSB7XG4gICAgICBkb2N1bWVudC5hY3RpdmVFbGVtZW50LmJsdXIoKTtcbiAgICB9XG4gIH07XG5cbiAgcmVuZGVyKCkge1xuICAgIGNvbnN0IHsgY2hpbGRyZW4sIGlzRW5hYmxlZCB9ID0gdGhpcy5wcm9wcztcbiAgICBjb25zdCB7IHRvdWNoU2Nyb2xsVGFyZ2V0IH0gPSB0aGlzLnN0YXRlO1xuXG4gICAgLy8gYmFpbCBlYXJseSBpZiBub3QgZW5hYmxlZFxuICAgIGlmICghaXNFbmFibGVkKSByZXR1cm4gY2hpbGRyZW47XG5cbiAgICAvKlxuICAgICAqIERpdlxuICAgICAqIC0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLVxuICAgICAqIGJsb2NrcyBzY3JvbGxpbmcgb24gbm9uLWJvZHkgZWxlbWVudHMgYmVoaW5kIHRoZSBtZW51XG5cbiAgICAgKiBOb2RlUmVzb2x2ZXJcbiAgICAgKiAtLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS1cbiAgICAgKiB3ZSBuZWVkIGEgcmVmZXJlbmNlIHRvIHRoZSBzY3JvbGxhYmxlIGVsZW1lbnQgdG8gXCJ1bmxvY2tcIiBzY3JvbGwgb25cbiAgICAgKiBtb2JpbGUgZGV2aWNlc1xuXG4gICAgICogU2Nyb2xsTG9ja1xuICAgICAqIC0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLVxuICAgICAqIGFjdHVhbGx5IGRvZXMgdGhlIHNjcm9sbCBsb2NraW5nXG4gICAgICovXG4gICAgcmV0dXJuIChcbiAgICAgIDxkaXY+XG4gICAgICAgIDxkaXZcbiAgICAgICAgICBvbkNsaWNrPXt0aGlzLmJsdXJTZWxlY3RJbnB1dH1cbiAgICAgICAgICBjc3M9e3sgcG9zaXRpb246ICdmaXhlZCcsIGxlZnQ6IDAsIGJvdHRvbTogMCwgcmlnaHQ6IDAsIHRvcDogMCB9fVxuICAgICAgICAvPlxuICAgICAgICA8Tm9kZVJlc29sdmVyIGlubmVyUmVmPXt0aGlzLmdldFNjcm9sbFRhcmdldH0+e2NoaWxkcmVufTwvTm9kZVJlc29sdmVyPlxuICAgICAgICB7dG91Y2hTY3JvbGxUYXJnZXQgPyAoXG4gICAgICAgICAgPFNjcm9sbExvY2sgdG91Y2hTY3JvbGxUYXJnZXQ9e3RvdWNoU2Nyb2xsVGFyZ2V0fSAvPlxuICAgICAgICApIDogbnVsbH1cbiAgICAgIDwvZGl2PlxuICAgICk7XG4gIH1cbn1cbiJdfQ== */"
  };

  // NOTE:
  // We shouldn't need this after updating to React v16.3.0, which introduces:
  // - createRef() https://reactjs.org/docs/react-api.html#reactcreateref
  // - forwardRef() https://reactjs.org/docs/react-api.html#reactforwardref
  var ScrollBlock =
  /*#__PURE__*/
  function (_PureComponent) {
    _inheritsLoose$2(ScrollBlock, _PureComponent);

    function ScrollBlock() {
      var _this;

      for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
        args[_key] = arguments[_key];
      }

      _this = _PureComponent.call.apply(_PureComponent, [this].concat(args)) || this;
      _this.state = {
        touchScrollTarget: null
      };

      _this.getScrollTarget = function (ref) {
        if (ref === _this.state.touchScrollTarget) return;

        _this.setState({
          touchScrollTarget: ref
        });
      };

      _this.blurSelectInput = function () {
        if (document.activeElement) {
          document.activeElement.blur();
        }
      };

      return _this;
    }

    var _proto = ScrollBlock.prototype;

    _proto.render = function render() {
      var _this$props = this.props,
          children = _this$props.children,
          isEnabled = _this$props.isEnabled;
      var touchScrollTarget = this.state.touchScrollTarget; // bail early if not enabled

      if (!isEnabled) return children;
      /*
       * Div
       * ------------------------------
       * blocks scrolling on non-body elements behind the menu
        * NodeResolver
       * ------------------------------
       * we need a reference to the scrollable element to "unlock" scroll on
       * mobile devices
        * ScrollLock
       * ------------------------------
       * actually does the scroll locking
       */

      return core.jsx("div", null, core.jsx("div", {
        onClick: this.blurSelectInput,
        css: _ref$1
      }), core.jsx(NodeResolver, {
        innerRef: this.getScrollTarget
      }, children), touchScrollTarget ? core.jsx(ScrollLock, {
        touchScrollTarget: touchScrollTarget
      }) : null);
    };

    return ScrollBlock;
  }(React.PureComponent);

  function _objectWithoutPropertiesLoose$1$1(source, excluded) { if (source == null) return {}; var target = {}; var sourceKeys = Object.keys(source); var key, i; for (i = 0; i < sourceKeys.length; i++) { key = sourceKeys[i]; if (excluded.indexOf(key) >= 0) continue; target[key] = source[key]; } return target; }

  function _inheritsLoose$3(subClass, superClass) { subClass.prototype = Object.create(superClass.prototype); subClass.prototype.constructor = subClass; subClass.__proto__ = superClass; }

  var ScrollCaptor =
  /*#__PURE__*/
  function (_Component) {
    _inheritsLoose$3(ScrollCaptor, _Component);

    function ScrollCaptor() {
      var _this;

      for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
        args[_key] = arguments[_key];
      }

      _this = _Component.call.apply(_Component, [this].concat(args)) || this;
      _this.isBottom = false;
      _this.isTop = false;
      _this.scrollTarget = void 0;
      _this.touchStart = void 0;

      _this.cancelScroll = function (event) {
        event.preventDefault();
        event.stopPropagation();
      };

      _this.handleEventDelta = function (event, delta) {
        var _this$props = _this.props,
            onBottomArrive = _this$props.onBottomArrive,
            onBottomLeave = _this$props.onBottomLeave,
            onTopArrive = _this$props.onTopArrive,
            onTopLeave = _this$props.onTopLeave;
        var _this$scrollTarget = _this.scrollTarget,
            scrollTop = _this$scrollTarget.scrollTop,
            scrollHeight = _this$scrollTarget.scrollHeight,
            clientHeight = _this$scrollTarget.clientHeight;
        var target = _this.scrollTarget;
        var isDeltaPositive = delta > 0;
        var availableScroll = scrollHeight - clientHeight - scrollTop;
        var shouldCancelScroll = false; // reset bottom/top flags

        if (availableScroll > delta && _this.isBottom) {
          if (onBottomLeave) onBottomLeave(event);
          _this.isBottom = false;
        }

        if (isDeltaPositive && _this.isTop) {
          if (onTopLeave) onTopLeave(event);
          _this.isTop = false;
        } // bottom limit


        if (isDeltaPositive && delta > availableScroll) {
          if (onBottomArrive && !_this.isBottom) {
            onBottomArrive(event);
          }

          target.scrollTop = scrollHeight;
          shouldCancelScroll = true;
          _this.isBottom = true; // top limit
        } else if (!isDeltaPositive && -delta > scrollTop) {
          if (onTopArrive && !_this.isTop) {
            onTopArrive(event);
          }

          target.scrollTop = 0;
          shouldCancelScroll = true;
          _this.isTop = true;
        } // cancel scroll


        if (shouldCancelScroll) {
          _this.cancelScroll(event);
        }
      };

      _this.onWheel = function (event) {
        _this.handleEventDelta(event, event.deltaY);
      };

      _this.onTouchStart = function (event) {
        // set touch start so we can calculate touchmove delta
        _this.touchStart = event.changedTouches[0].clientY;
      };

      _this.onTouchMove = function (event) {
        var deltaY = _this.touchStart - event.changedTouches[0].clientY;

        _this.handleEventDelta(event, deltaY);
      };

      _this.getScrollTarget = function (ref) {
        _this.scrollTarget = ref;
      };

      return _this;
    }

    var _proto = ScrollCaptor.prototype;

    _proto.componentDidMount = function componentDidMount() {
      this.startListening(this.scrollTarget);
    };

    _proto.componentWillUnmount = function componentWillUnmount() {
      this.stopListening(this.scrollTarget);
    };

    _proto.startListening = function startListening(el) {
      // bail early if no element is available to attach to
      if (!el) return; // all the if statements are to appease Flow 😢

      if (typeof el.addEventListener === 'function') {
        el.addEventListener('wheel', this.onWheel, false);
      }

      if (typeof el.addEventListener === 'function') {
        el.addEventListener('touchstart', this.onTouchStart, false);
      }

      if (typeof el.addEventListener === 'function') {
        el.addEventListener('touchmove', this.onTouchMove, false);
      }
    };

    _proto.stopListening = function stopListening(el) {
      // all the if statements are to appease Flow 😢
      if (typeof el.removeEventListener === 'function') {
        el.removeEventListener('wheel', this.onWheel, false);
      }

      if (typeof el.removeEventListener === 'function') {
        el.removeEventListener('touchstart', this.onTouchStart, false);
      }

      if (typeof el.removeEventListener === 'function') {
        el.removeEventListener('touchmove', this.onTouchMove, false);
      }
    };

    _proto.render = function render() {
      return React__default.createElement(NodeResolver, {
        innerRef: this.getScrollTarget
      }, this.props.children);
    };

    return ScrollCaptor;
  }(React.Component);

  function ScrollCaptorSwitch(_ref) {
    var _ref$isEnabled = _ref.isEnabled,
        isEnabled = _ref$isEnabled === void 0 ? true : _ref$isEnabled,
        props = _objectWithoutPropertiesLoose$1$1(_ref, ["isEnabled"]);

    return isEnabled ? React__default.createElement(ScrollCaptor, props) : props.children;
  }

  var instructionsAriaMessage = function instructionsAriaMessage(event, context) {
    if (context === void 0) {
      context = {};
    }

    var _context = context,
        isSearchable = _context.isSearchable,
        isMulti = _context.isMulti,
        label = _context.label,
        isDisabled = _context.isDisabled;

    switch (event) {
      case 'menu':
        return "Use Up and Down to choose options" + (isDisabled ? '' : ', press Enter to select the currently focused option') + ", press Escape to exit the menu, press Tab to select the option and exit the menu.";

      case 'input':
        return (label ? label : 'Select') + " is focused " + (isSearchable ? ',type to refine list' : '') + ", press Down to open the menu, " + (isMulti ? ' press left to focus selected values' : '');

      case 'value':
        return 'Use left and right to toggle between focused values, press Backspace to remove the currently focused value';
    }
  };
  var valueEventAriaMessage = function valueEventAriaMessage(event, context) {
    var value = context.value,
        isDisabled = context.isDisabled;
    if (!value) return;

    switch (event) {
      case 'deselect-option':
      case 'pop-value':
      case 'remove-value':
        return "option " + value + ", deselected.";

      case 'select-option':
        return isDisabled ? "option " + value + " is disabled. Select another option." : "option " + value + ", selected.";
    }
  };
  var valueFocusAriaMessage = function valueFocusAriaMessage(_ref) {
    var focusedValue = _ref.focusedValue,
        getOptionLabel = _ref.getOptionLabel,
        selectValue = _ref.selectValue;
    return "value " + getOptionLabel(focusedValue) + " focused, " + (selectValue.indexOf(focusedValue) + 1) + " of " + selectValue.length + ".";
  };
  var optionFocusAriaMessage = function optionFocusAriaMessage(_ref2) {
    var focusedOption = _ref2.focusedOption,
        getOptionLabel = _ref2.getOptionLabel,
        options = _ref2.options;
    return "option " + getOptionLabel(focusedOption) + " focused" + (focusedOption.isDisabled ? ' disabled' : '') + ", " + (options.indexOf(focusedOption) + 1) + " of " + options.length + ".";
  };
  var resultsAriaMessage = function resultsAriaMessage(_ref3) {
    var inputValue = _ref3.inputValue,
        screenReaderMessage = _ref3.screenReaderMessage;
    return "" + screenReaderMessage + (inputValue ? ' for search term ' + inputValue : '') + ".";
  };

  var formatGroupLabel = function formatGroupLabel(group) {
    return group.label;
  };
  var getOptionLabel = function getOptionLabel(option) {
    return option.label;
  };
  var getOptionValue = function getOptionValue(option) {
    return option.value;
  };
  var isOptionDisabled = function isOptionDisabled(option) {
    return !!option.isDisabled;
  };
  var defaultStyles = {
    clearIndicator: clearIndicatorCSS,
    container: containerCSS,
    control: css$1,
    dropdownIndicator: dropdownIndicatorCSS,
    group: groupCSS,
    groupHeading: groupHeadingCSS,
    indicatorsContainer: indicatorsContainerCSS,
    indicatorSeparator: indicatorSeparatorCSS,
    input: inputCSS,
    loadingIndicator: loadingIndicatorCSS,
    loadingMessage: loadingMessageCSS,
    menu: menuCSS,
    menuList: menuListCSS,
    menuPortal: menuPortalCSS,
    multiValue: multiValueCSS,
    multiValueLabel: multiValueLabelCSS,
    multiValueRemove: multiValueRemoveCSS,
    noOptionsMessage: noOptionsMessageCSS,
    option: optionCSS,
    placeholder: placeholderCSS,
    singleValue: css$1$1,
    valueContainer: valueContainerCSS
  }; // Merge Utility

  var colors = {
    primary: '#2684FF',
    primary75: '#4C9AFF',
    primary50: '#B2D4FF',
    primary25: '#DEEBFF',
    danger: '#DE350B',
    dangerLight: '#FFBDAD',
    neutral0: 'hsl(0, 0%, 100%)',
    neutral5: 'hsl(0, 0%, 95%)',
    neutral10: 'hsl(0, 0%, 90%)',
    neutral20: 'hsl(0, 0%, 80%)',
    neutral30: 'hsl(0, 0%, 70%)',
    neutral40: 'hsl(0, 0%, 60%)',
    neutral50: 'hsl(0, 0%, 50%)',
    neutral60: 'hsl(0, 0%, 40%)',
    neutral70: 'hsl(0, 0%, 30%)',
    neutral80: 'hsl(0, 0%, 20%)',
    neutral90: 'hsl(0, 0%, 10%)'
  };
  var borderRadius = 4; // Used to calculate consistent margin/padding on elements

  var baseUnit = 4; // The minimum height of the control

  var controlHeight = 38; // The amount of space between the control and menu */

  var menuGutter = baseUnit * 2;
  var spacing = {
    baseUnit: baseUnit,
    controlHeight: controlHeight,
    menuGutter: menuGutter
  };
  var defaultTheme = {
    borderRadius: borderRadius,
    colors: colors,
    spacing: spacing
  };

  function _objectWithoutPropertiesLoose$2$1(source, excluded) { if (source == null) return {}; var target = {}; var sourceKeys = Object.keys(source); var key, i; for (i = 0; i < sourceKeys.length; i++) { key = sourceKeys[i]; if (excluded.indexOf(key) >= 0) continue; target[key] = source[key]; } return target; }

  function _extends$4$1() { _extends$4$1 = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; }; return _extends$4$1.apply(this, arguments); }

  function _inheritsLoose$4(subClass, superClass) { subClass.prototype = Object.create(superClass.prototype); subClass.prototype.constructor = subClass; subClass.__proto__ = superClass; }

  function _assertThisInitialized(self) { if (self === void 0) { throw new ReferenceError("this hasn't been initialised - super() hasn't been called"); } return self; }
  var defaultProps = {
    backspaceRemovesValue: true,
    blurInputOnSelect: isTouchCapable(),
    captureMenuScroll: !isTouchCapable(),
    closeMenuOnSelect: true,
    closeMenuOnScroll: false,
    components: {},
    controlShouldRenderValue: true,
    escapeClearsValue: false,
    filterOption: createFilter(),
    formatGroupLabel: formatGroupLabel,
    getOptionLabel: getOptionLabel,
    getOptionValue: getOptionValue,
    isDisabled: false,
    isLoading: false,
    isMulti: false,
    isRtl: false,
    isSearchable: true,
    isOptionDisabled: isOptionDisabled,
    loadingMessage: function loadingMessage() {
      return 'Loading...';
    },
    maxMenuHeight: 300,
    minMenuHeight: 140,
    menuIsOpen: false,
    menuPlacement: 'bottom',
    menuPosition: 'absolute',
    menuShouldBlockScroll: false,
    menuShouldScrollIntoView: !isMobileDevice(),
    noOptionsMessage: function noOptionsMessage() {
      return 'No options';
    },
    openMenuOnFocus: false,
    openMenuOnClick: true,
    options: [],
    pageSize: 5,
    placeholder: 'Select...',
    screenReaderStatus: function screenReaderStatus(_ref) {
      var count = _ref.count;
      return count + " result" + (count !== 1 ? 's' : '') + " available";
    },
    styles: {},
    tabIndex: '0',
    tabSelectsValue: true
  };
  var instanceId = 1;

  var Select =
  /*#__PURE__*/
  function (_Component) {
    _inheritsLoose$4(Select, _Component);

    // Misc. Instance Properties
    // ------------------------------
    // TODO
    // Refs
    // ------------------------------
    // Lifecycle
    // ------------------------------
    function Select(_props) {
      var _this;

      _this = _Component.call(this, _props) || this;
      _this.state = {
        ariaLiveSelection: '',
        ariaLiveContext: '',
        focusedOption: null,
        focusedValue: null,
        inputIsHidden: false,
        isFocused: false,
        menuOptions: {
          render: [],
          focusable: []
        },
        selectValue: []
      };
      _this.blockOptionHover = false;
      _this.isComposing = false;
      _this.clearFocusValueOnUpdate = false;
      _this.commonProps = void 0;
      _this.components = void 0;
      _this.hasGroups = false;
      _this.initialTouchX = 0;
      _this.initialTouchY = 0;
      _this.inputIsHiddenAfterUpdate = void 0;
      _this.instancePrefix = '';
      _this.openAfterFocus = false;
      _this.scrollToFocusedOptionOnUpdate = false;
      _this.userIsDragging = void 0;
      _this.controlRef = null;

      _this.getControlRef = function (ref) {
        _this.controlRef = ref;
      };

      _this.focusedOptionRef = null;

      _this.getFocusedOptionRef = function (ref) {
        _this.focusedOptionRef = ref;
      };

      _this.menuListRef = null;

      _this.getMenuListRef = function (ref) {
        _this.menuListRef = ref;
      };

      _this.inputRef = null;

      _this.getInputRef = function (ref) {
        _this.inputRef = ref;
      };

      _this.cacheComponents = function (components) {
        _this.components = defaultComponents({
          components: components
        });
      };

      _this.focus = _this.focusInput;
      _this.blur = _this.blurInput;

      _this.onChange = function (newValue, actionMeta) {
        var _this$props = _this.props,
            onChange = _this$props.onChange,
            name = _this$props.name;
        onChange(newValue, _extends$4$1({}, actionMeta, {
          name: name
        }));
      };

      _this.setValue = function (newValue, action, option) {
        if (action === void 0) {
          action = 'set-value';
        }

        var _this$props2 = _this.props,
            closeMenuOnSelect = _this$props2.closeMenuOnSelect,
            isMulti = _this$props2.isMulti;

        _this.onInputChange('', {
          action: 'set-value'
        });

        if (closeMenuOnSelect) {
          _this.inputIsHiddenAfterUpdate = !isMulti;

          _this.onMenuClose();
        } // when the select value should change, we should reset focusedValue


        _this.clearFocusValueOnUpdate = true;

        _this.onChange(newValue, {
          action: action,
          option: option
        });
      };

      _this.selectOption = function (newValue) {
        var _this$props3 = _this.props,
            blurInputOnSelect = _this$props3.blurInputOnSelect,
            isMulti = _this$props3.isMulti;
        var selectValue = _this.state.selectValue;

        if (isMulti) {
          if (_this.isOptionSelected(newValue, selectValue)) {
            var candidate = _this.getOptionValue(newValue);

            _this.setValue(selectValue.filter(function (i) {
              return _this.getOptionValue(i) !== candidate;
            }), 'deselect-option', newValue);

            _this.announceAriaLiveSelection({
              event: 'deselect-option',
              context: {
                value: _this.getOptionLabel(newValue)
              }
            });
          } else {
            if (!_this.isOptionDisabled(newValue, selectValue)) {
              _this.setValue([].concat(selectValue, [newValue]), 'select-option', newValue);

              _this.announceAriaLiveSelection({
                event: 'select-option',
                context: {
                  value: _this.getOptionLabel(newValue)
                }
              });
            } else {
              // announce that option is disabled
              _this.announceAriaLiveSelection({
                event: 'select-option',
                context: {
                  value: _this.getOptionLabel(newValue),
                  isDisabled: true
                }
              });
            }
          }
        } else {
          if (!_this.isOptionDisabled(newValue, selectValue)) {
            _this.setValue(newValue, 'select-option');

            _this.announceAriaLiveSelection({
              event: 'select-option',
              context: {
                value: _this.getOptionLabel(newValue)
              }
            });
          } else {
            // announce that option is disabled
            _this.announceAriaLiveSelection({
              event: 'select-option',
              context: {
                value: _this.getOptionLabel(newValue),
                isDisabled: true
              }
            });
          }
        }

        if (blurInputOnSelect) {
          _this.blurInput();
        }
      };

      _this.removeValue = function (removedValue) {
        var selectValue = _this.state.selectValue;

        var candidate = _this.getOptionValue(removedValue);

        var newValue = selectValue.filter(function (i) {
          return _this.getOptionValue(i) !== candidate;
        });

        _this.onChange(newValue.length ? newValue : null, {
          action: 'remove-value',
          removedValue: removedValue
        });

        _this.announceAriaLiveSelection({
          event: 'remove-value',
          context: {
            value: removedValue ? _this.getOptionLabel(removedValue) : ''
          }
        });

        _this.focusInput();
      };

      _this.clearValue = function () {
        var isMulti = _this.props.isMulti;

        _this.onChange(isMulti ? [] : null, {
          action: 'clear'
        });
      };

      _this.popValue = function () {
        var selectValue = _this.state.selectValue;
        var lastSelectedValue = selectValue[selectValue.length - 1];
        var newValue = selectValue.slice(0, selectValue.length - 1);

        _this.announceAriaLiveSelection({
          event: 'pop-value',
          context: {
            value: lastSelectedValue ? _this.getOptionLabel(lastSelectedValue) : ''
          }
        });

        _this.onChange(newValue.length ? newValue : null, {
          action: 'pop-value',
          removedValue: lastSelectedValue
        });
      };

      _this.getOptionLabel = function (data) {
        return _this.props.getOptionLabel(data);
      };

      _this.getOptionValue = function (data) {
        return _this.props.getOptionValue(data);
      };

      _this.getStyles = function (key, props) {
        var base = defaultStyles[key](props);
        base.boxSizing = 'border-box';
        var custom = _this.props.styles[key];
        return custom ? custom(base, props) : base;
      };

      _this.getElementId = function (element) {
        return _this.instancePrefix + "-" + element;
      };

      _this.getActiveDescendentId = function () {
        var menuIsOpen = _this.props.menuIsOpen;
        var _this$state = _this.state,
            menuOptions = _this$state.menuOptions,
            focusedOption = _this$state.focusedOption;
        if (!focusedOption || !menuIsOpen) return undefined;
        var index = menuOptions.focusable.indexOf(focusedOption);
        var option = menuOptions.render[index];
        return option && option.key;
      };

      _this.announceAriaLiveSelection = function (_ref2) {
        var event = _ref2.event,
            context = _ref2.context;

        _this.setState({
          ariaLiveSelection: valueEventAriaMessage(event, context)
        });
      };

      _this.announceAriaLiveContext = function (_ref3) {
        var event = _ref3.event,
            context = _ref3.context;

        _this.setState({
          ariaLiveContext: instructionsAriaMessage(event, _extends$4$1({}, context, {
            label: _this.props['aria-label']
          }))
        });
      };

      _this.onMenuMouseDown = function (event) {
        if (event.button !== 0) {
          return;
        }

        event.stopPropagation();
        event.preventDefault();

        _this.focusInput();
      };

      _this.onMenuMouseMove = function (event) {
        _this.blockOptionHover = false;
      };

      _this.onControlMouseDown = function (event) {
        var openMenuOnClick = _this.props.openMenuOnClick;

        if (!_this.state.isFocused) {
          if (openMenuOnClick) {
            _this.openAfterFocus = true;
          }

          _this.focusInput();
        } else if (!_this.props.menuIsOpen) {
          if (openMenuOnClick) {
            _this.openMenu('first');
          }
        } else {
          if ( // $FlowFixMe
          event.target.tagName !== 'INPUT' && event.target.tagName !== 'TEXTAREA') {
            _this.onMenuClose();
          }
        }

        if ( // $FlowFixMe
        event.target.tagName !== 'INPUT' && event.target.tagName !== 'TEXTAREA') {
          event.preventDefault();
        }
      };

      _this.onDropdownIndicatorMouseDown = function (event) {
        // ignore mouse events that weren't triggered by the primary button
        if (event && event.type === 'mousedown' && event.button !== 0) {
          return;
        }

        if (_this.props.isDisabled) return;
        var _this$props4 = _this.props,
            isMulti = _this$props4.isMulti,
            menuIsOpen = _this$props4.menuIsOpen;

        _this.focusInput();

        if (menuIsOpen) {
          _this.inputIsHiddenAfterUpdate = !isMulti;

          _this.onMenuClose();
        } else {
          _this.openMenu('first');
        }

        event.preventDefault();
        event.stopPropagation();
      };

      _this.onClearIndicatorMouseDown = function (event) {
        // ignore mouse events that weren't triggered by the primary button
        if (event && event.type === 'mousedown' && event.button !== 0) {
          return;
        }

        _this.clearValue();

        event.stopPropagation();
        _this.openAfterFocus = false;

        if (event.type === 'touchend') {
          _this.focusInput();
        } else {
          setTimeout(function () {
            return _this.focusInput();
          });
        }
      };

      _this.onScroll = function (event) {
        if (typeof _this.props.closeMenuOnScroll === 'boolean') {
          if (event.target instanceof HTMLElement && isDocumentElement(event.target)) {
            _this.props.onMenuClose();
          }
        } else if (typeof _this.props.closeMenuOnScroll === 'function') {
          if (_this.props.closeMenuOnScroll(event)) {
            _this.props.onMenuClose();
          }
        }
      };

      _this.onCompositionStart = function () {
        _this.isComposing = true;
      };

      _this.onCompositionEnd = function () {
        _this.isComposing = false;
      };

      _this.onTouchStart = function (_ref4) {
        var touches = _ref4.touches;
        var touch = touches.item(0);

        if (!touch) {
          return;
        }

        _this.initialTouchX = touch.clientX;
        _this.initialTouchY = touch.clientY;
        _this.userIsDragging = false;
      };

      _this.onTouchMove = function (_ref5) {
        var touches = _ref5.touches;
        var touch = touches.item(0);

        if (!touch) {
          return;
        }

        var deltaX = Math.abs(touch.clientX - _this.initialTouchX);
        var deltaY = Math.abs(touch.clientY - _this.initialTouchY);
        var moveThreshold = 5;
        _this.userIsDragging = deltaX > moveThreshold || deltaY > moveThreshold;
      };

      _this.onTouchEnd = function (event) {
        if (_this.userIsDragging) return; // close the menu if the user taps outside
        // we're checking on event.target here instead of event.currentTarget, because we want to assert information
        // on events on child elements, not the document (which we've attached this handler to).

        if (_this.controlRef && !_this.controlRef.contains(event.target) && _this.menuListRef && !_this.menuListRef.contains(event.target)) {
          _this.blurInput();
        } // reset move vars


        _this.initialTouchX = 0;
        _this.initialTouchY = 0;
      };

      _this.onControlTouchEnd = function (event) {
        if (_this.userIsDragging) return;

        _this.onControlMouseDown(event);
      };

      _this.onClearIndicatorTouchEnd = function (event) {
        if (_this.userIsDragging) return;

        _this.onClearIndicatorMouseDown(event);
      };

      _this.onDropdownIndicatorTouchEnd = function (event) {
        if (_this.userIsDragging) return;

        _this.onDropdownIndicatorMouseDown(event);
      };

      _this.handleInputChange = function (event) {
        var inputValue = event.currentTarget.value;
        _this.inputIsHiddenAfterUpdate = false;

        _this.onInputChange(inputValue, {
          action: 'input-change'
        });

        _this.onMenuOpen();
      };

      _this.onInputFocus = function (event) {
        var _this$props5 = _this.props,
            isSearchable = _this$props5.isSearchable,
            isMulti = _this$props5.isMulti;

        if (_this.props.onFocus) {
          _this.props.onFocus(event);
        }

        _this.inputIsHiddenAfterUpdate = false;

        _this.announceAriaLiveContext({
          event: 'input',
          context: {
            isSearchable: isSearchable,
            isMulti: isMulti
          }
        });

        _this.setState({
          isFocused: true
        });

        if (_this.openAfterFocus || _this.props.openMenuOnFocus) {
          _this.openMenu('first');
        }

        _this.openAfterFocus = false;
      };

      _this.onInputBlur = function (event) {
        if (_this.menuListRef && _this.menuListRef.contains(document.activeElement)) {
          _this.inputRef.focus();

          return;
        }

        if (_this.props.onBlur) {
          _this.props.onBlur(event);
        }

        _this.onInputChange('', {
          action: 'input-blur'
        });

        _this.onMenuClose();

        _this.setState({
          focusedValue: null,
          isFocused: false
        });
      };

      _this.onOptionHover = function (focusedOption) {
        if (_this.blockOptionHover || _this.state.focusedOption === focusedOption) {
          return;
        }

        _this.setState({
          focusedOption: focusedOption
        });
      };

      _this.shouldHideSelectedOptions = function () {
        var _this$props6 = _this.props,
            hideSelectedOptions = _this$props6.hideSelectedOptions,
            isMulti = _this$props6.isMulti;
        if (hideSelectedOptions === undefined) return isMulti;
        return hideSelectedOptions;
      };

      _this.onKeyDown = function (event) {
        var _this$props7 = _this.props,
            isMulti = _this$props7.isMulti,
            backspaceRemovesValue = _this$props7.backspaceRemovesValue,
            escapeClearsValue = _this$props7.escapeClearsValue,
            inputValue = _this$props7.inputValue,
            isClearable = _this$props7.isClearable,
            isDisabled = _this$props7.isDisabled,
            menuIsOpen = _this$props7.menuIsOpen,
            onKeyDown = _this$props7.onKeyDown,
            tabSelectsValue = _this$props7.tabSelectsValue,
            openMenuOnFocus = _this$props7.openMenuOnFocus;
        var _this$state2 = _this.state,
            focusedOption = _this$state2.focusedOption,
            focusedValue = _this$state2.focusedValue,
            selectValue = _this$state2.selectValue;
        if (isDisabled) return;

        if (typeof onKeyDown === 'function') {
          onKeyDown(event);

          if (event.defaultPrevented) {
            return;
          }
        } // Block option hover events when the user has just pressed a key


        _this.blockOptionHover = true;

        switch (event.key) {
          case 'ArrowLeft':
            if (!isMulti || inputValue) return;

            _this.focusValue('previous');

            break;

          case 'ArrowRight':
            if (!isMulti || inputValue) return;

            _this.focusValue('next');

            break;

          case 'Delete':
          case 'Backspace':
            if (inputValue) return;

            if (focusedValue) {
              _this.removeValue(focusedValue);
            } else {
              if (!backspaceRemovesValue) return;

              if (isMulti) {
                _this.popValue();
              } else if (isClearable) {
                _this.clearValue();
              }
            }

            break;

          case 'Tab':
            if (_this.isComposing) return;

            if (event.shiftKey || !menuIsOpen || !tabSelectsValue || !focusedOption || // don't capture the event if the menu opens on focus and the focused
            // option is already selected; it breaks the flow of navigation
            openMenuOnFocus && _this.isOptionSelected(focusedOption, selectValue)) {
              return;
            }

            _this.selectOption(focusedOption);

            break;

          case 'Enter':
            if (event.keyCode === 229) {
              // ignore the keydown event from an Input Method Editor(IME)
              // ref. https://www.w3.org/TR/uievents/#determine-keydown-keyup-keyCode
              break;
            }

            if (menuIsOpen) {
              if (!focusedOption) return;
              if (_this.isComposing) return;

              _this.selectOption(focusedOption);

              break;
            }

            return;

          case 'Escape':
            if (menuIsOpen) {
              _this.inputIsHiddenAfterUpdate = false;

              _this.onInputChange('', {
                action: 'menu-close'
              });

              _this.onMenuClose();
            } else if (isClearable && escapeClearsValue) {
              _this.clearValue();
            }

            break;

          case ' ':
            // space
            if (inputValue) {
              return;
            }

            if (!menuIsOpen) {
              _this.openMenu('first');

              break;
            }

            if (!focusedOption) return;

            _this.selectOption(focusedOption);

            break;

          case 'ArrowUp':
            if (menuIsOpen) {
              _this.focusOption('up');
            } else {
              _this.openMenu('last');
            }

            break;

          case 'ArrowDown':
            if (menuIsOpen) {
              _this.focusOption('down');
            } else {
              _this.openMenu('first');
            }

            break;

          case 'PageUp':
            if (!menuIsOpen) return;

            _this.focusOption('pageup');

            break;

          case 'PageDown':
            if (!menuIsOpen) return;

            _this.focusOption('pagedown');

            break;

          case 'Home':
            if (!menuIsOpen) return;

            _this.focusOption('first');

            break;

          case 'End':
            if (!menuIsOpen) return;

            _this.focusOption('last');

            break;

          default:
            return;
        }

        event.preventDefault();
      };

      _this.buildMenuOptions = function (props, selectValue) {
        var _props$inputValue = props.inputValue,
            inputValue = _props$inputValue === void 0 ? '' : _props$inputValue,
            options = props.options;

        var toOption = function toOption(option, id) {
          var isDisabled = _this.isOptionDisabled(option, selectValue);

          var isSelected = _this.isOptionSelected(option, selectValue);

          var label = _this.getOptionLabel(option);

          var value = _this.getOptionValue(option);

          if (_this.shouldHideSelectedOptions() && isSelected || !_this.filterOption({
            label: label,
            value: value,
            data: option
          }, inputValue)) {
            return;
          }

          var onHover = isDisabled ? undefined : function () {
            return _this.onOptionHover(option);
          };
          var onSelect = isDisabled ? undefined : function () {
            return _this.selectOption(option);
          };
          var optionId = _this.getElementId('option') + "-" + id;
          return {
            innerProps: {
              id: optionId,
              onClick: onSelect,
              onMouseMove: onHover,
              onMouseOver: onHover,
              tabIndex: -1
            },
            data: option,
            isDisabled: isDisabled,
            isSelected: isSelected,
            key: optionId,
            label: label,
            type: 'option',
            value: value
          };
        };

        return options.reduce(function (acc, item, itemIndex) {
          if (item.options) {
            // TODO needs a tidier implementation
            if (!_this.hasGroups) _this.hasGroups = true;
            var items = item.options;
            var children = items.map(function (child, i) {
              var option = toOption(child, itemIndex + "-" + i);
              if (option) acc.focusable.push(child);
              return option;
            }).filter(Boolean);

            if (children.length) {
              var groupId = _this.getElementId('group') + "-" + itemIndex;
              acc.render.push({
                type: 'group',
                key: groupId,
                data: item,
                options: children
              });
            }
          } else {
            var option = toOption(item, "" + itemIndex);

            if (option) {
              acc.render.push(option);
              acc.focusable.push(item);
            }
          }

          return acc;
        }, {
          render: [],
          focusable: []
        });
      };

      var _value = _props.value;
      _this.cacheComponents = memoizeOne(_this.cacheComponents, exportedEqual).bind(_assertThisInitialized(_assertThisInitialized(_this)));

      _this.cacheComponents(_props.components);

      _this.instancePrefix = 'react-select-' + (_this.props.instanceId || ++instanceId);

      var _selectValue = cleanValue(_value);

      _this.buildMenuOptions = memoizeOne(_this.buildMenuOptions, function (newArgs, lastArgs) {
        var _ref6 = newArgs,
            newProps = _ref6[0],
            newSelectValue = _ref6[1];
        var _ref7 = lastArgs,
            lastProps = _ref7[0],
            lastSelectValue = _ref7[1];
        return exportedEqual(newSelectValue, lastSelectValue) && exportedEqual(newProps.inputValue, lastProps.inputValue) && exportedEqual(newProps.options, lastProps.options);
      }).bind(_assertThisInitialized(_assertThisInitialized(_this)));

      var _menuOptions = _props.menuIsOpen ? _this.buildMenuOptions(_props, _selectValue) : {
        render: [],
        focusable: []
      };

      _this.state.menuOptions = _menuOptions;
      _this.state.selectValue = _selectValue;
      return _this;
    }

    var _proto = Select.prototype;

    _proto.componentDidMount = function componentDidMount() {
      this.startListeningComposition();
      this.startListeningToTouch();

      if (this.props.closeMenuOnScroll && document && document.addEventListener) {
        // Listen to all scroll events, and filter them out inside of 'onScroll'
        document.addEventListener('scroll', this.onScroll, true);
      }

      if (this.props.autoFocus) {
        this.focusInput();
      }
    };

    _proto.UNSAFE_componentWillReceiveProps = function UNSAFE_componentWillReceiveProps(nextProps) {
      var _this$props8 = this.props,
          options = _this$props8.options,
          value = _this$props8.value,
          menuIsOpen = _this$props8.menuIsOpen,
          inputValue = _this$props8.inputValue; // re-cache custom components

      this.cacheComponents(nextProps.components); // rebuild the menu options

      if (nextProps.value !== value || nextProps.options !== options || nextProps.menuIsOpen !== menuIsOpen || nextProps.inputValue !== inputValue) {
        var selectValue = cleanValue(nextProps.value);
        var menuOptions = nextProps.menuIsOpen ? this.buildMenuOptions(nextProps, selectValue) : {
          render: [],
          focusable: []
        };
        var focusedValue = this.getNextFocusedValue(selectValue);
        var focusedOption = this.getNextFocusedOption(menuOptions.focusable);
        this.setState({
          menuOptions: menuOptions,
          selectValue: selectValue,
          focusedOption: focusedOption,
          focusedValue: focusedValue
        });
      } // some updates should toggle the state of the input visibility


      if (this.inputIsHiddenAfterUpdate != null) {
        this.setState({
          inputIsHidden: this.inputIsHiddenAfterUpdate
        });
        delete this.inputIsHiddenAfterUpdate;
      }
    };

    _proto.componentDidUpdate = function componentDidUpdate(prevProps) {
      var _this$props9 = this.props,
          isDisabled = _this$props9.isDisabled,
          menuIsOpen = _this$props9.menuIsOpen;
      var isFocused = this.state.isFocused;

      if ( // ensure focus is restored correctly when the control becomes enabled
      isFocused && !isDisabled && prevProps.isDisabled || // ensure focus is on the Input when the menu opens
      isFocused && menuIsOpen && !prevProps.menuIsOpen) {
        this.focusInput();
      } // scroll the focused option into view if necessary


      if (this.menuListRef && this.focusedOptionRef && this.scrollToFocusedOptionOnUpdate) {
        scrollIntoView(this.menuListRef, this.focusedOptionRef);
        this.scrollToFocusedOptionOnUpdate = false;
      }
    };

    _proto.componentWillUnmount = function componentWillUnmount() {
      this.stopListeningComposition();
      this.stopListeningToTouch();
      document.removeEventListener('scroll', this.onScroll, true);
    };

    // ==============================
    // Consumer Handlers
    // ==============================
    _proto.onMenuOpen = function onMenuOpen() {
      this.props.onMenuOpen();
    };

    _proto.onMenuClose = function onMenuClose() {
      var _this$props10 = this.props,
          isSearchable = _this$props10.isSearchable,
          isMulti = _this$props10.isMulti;
      this.announceAriaLiveContext({
        event: 'input',
        context: {
          isSearchable: isSearchable,
          isMulti: isMulti
        }
      });
      this.onInputChange('', {
        action: 'menu-close'
      });
      this.props.onMenuClose();
    };

    _proto.onInputChange = function onInputChange(newValue, actionMeta) {
      this.props.onInputChange(newValue, actionMeta);
    } // ==============================
    // Methods
    // ==============================
    ;

    _proto.focusInput = function focusInput() {
      if (!this.inputRef) return;
      this.inputRef.focus();
    };

    _proto.blurInput = function blurInput() {
      if (!this.inputRef) return;
      this.inputRef.blur();
    } // aliased for consumers
    ;

    _proto.openMenu = function openMenu(focusOption) {
      var _this2 = this;

      var _this$state3 = this.state,
          selectValue = _this$state3.selectValue,
          isFocused = _this$state3.isFocused;
      var menuOptions = this.buildMenuOptions(this.props, selectValue);
      var isMulti = this.props.isMulti;
      var openAtIndex = focusOption === 'first' ? 0 : menuOptions.focusable.length - 1;

      if (!isMulti) {
        var selectedIndex = menuOptions.focusable.indexOf(selectValue[0]);

        if (selectedIndex > -1) {
          openAtIndex = selectedIndex;
        }
      } // only scroll if the menu isn't already open


      this.scrollToFocusedOptionOnUpdate = !(isFocused && this.menuListRef);
      this.inputIsHiddenAfterUpdate = false;
      this.setState({
        menuOptions: menuOptions,
        focusedValue: null,
        focusedOption: menuOptions.focusable[openAtIndex]
      }, function () {
        _this2.onMenuOpen();

        _this2.announceAriaLiveContext({
          event: 'menu'
        });
      });
    };

    _proto.focusValue = function focusValue(direction) {
      var _this$props11 = this.props,
          isMulti = _this$props11.isMulti,
          isSearchable = _this$props11.isSearchable;
      var _this$state4 = this.state,
          selectValue = _this$state4.selectValue,
          focusedValue = _this$state4.focusedValue; // Only multiselects support value focusing

      if (!isMulti) return;
      this.setState({
        focusedOption: null
      });
      var focusedIndex = selectValue.indexOf(focusedValue);

      if (!focusedValue) {
        focusedIndex = -1;
        this.announceAriaLiveContext({
          event: 'value'
        });
      }

      var lastIndex = selectValue.length - 1;
      var nextFocus = -1;
      if (!selectValue.length) return;

      switch (direction) {
        case 'previous':
          if (focusedIndex === 0) {
            // don't cycle from the start to the end
            nextFocus = 0;
          } else if (focusedIndex === -1) {
            // if nothing is focused, focus the last value first
            nextFocus = lastIndex;
          } else {
            nextFocus = focusedIndex - 1;
          }

          break;

        case 'next':
          if (focusedIndex > -1 && focusedIndex < lastIndex) {
            nextFocus = focusedIndex + 1;
          }

          break;
      }

      if (nextFocus === -1) {
        this.announceAriaLiveContext({
          event: 'input',
          context: {
            isSearchable: isSearchable,
            isMulti: isMulti
          }
        });
      }

      this.setState({
        inputIsHidden: nextFocus !== -1,
        focusedValue: selectValue[nextFocus]
      });
    };

    _proto.focusOption = function focusOption(direction) {
      if (direction === void 0) {
        direction = 'first';
      }

      var pageSize = this.props.pageSize;
      var _this$state5 = this.state,
          focusedOption = _this$state5.focusedOption,
          menuOptions = _this$state5.menuOptions;
      var options = menuOptions.focusable;
      if (!options.length) return;
      var nextFocus = 0; // handles 'first'

      var focusedIndex = options.indexOf(focusedOption);

      if (!focusedOption) {
        focusedIndex = -1;
        this.announceAriaLiveContext({
          event: 'menu'
        });
      }

      if (direction === 'up') {
        nextFocus = focusedIndex > 0 ? focusedIndex - 1 : options.length - 1;
      } else if (direction === 'down') {
        nextFocus = (focusedIndex + 1) % options.length;
      } else if (direction === 'pageup') {
        nextFocus = focusedIndex - pageSize;
        if (nextFocus < 0) nextFocus = 0;
      } else if (direction === 'pagedown') {
        nextFocus = focusedIndex + pageSize;
        if (nextFocus > options.length - 1) nextFocus = options.length - 1;
      } else if (direction === 'last') {
        nextFocus = options.length - 1;
      }

      this.scrollToFocusedOptionOnUpdate = true;
      this.setState({
        focusedOption: options[nextFocus],
        focusedValue: null
      });
      this.announceAriaLiveContext({
        event: 'menu',
        context: {
          isDisabled: isOptionDisabled(options[nextFocus])
        }
      });
    };

    // ==============================
    // Getters
    // ==============================
    _proto.getTheme = function getTheme() {
      // Use the default theme if there are no customizations.
      if (!this.props.theme) {
        return defaultTheme;
      } // If the theme prop is a function, assume the function
      // knows how to merge the passed-in default theme with
      // its own modifications.


      if (typeof this.props.theme === 'function') {
        return this.props.theme(defaultTheme);
      } // Otherwise, if a plain theme object was passed in,
      // overlay it with the default theme.


      return _extends$4$1({}, defaultTheme, this.props.theme);
    };

    _proto.getCommonProps = function getCommonProps() {
      var clearValue = this.clearValue,
          getStyles = this.getStyles,
          setValue = this.setValue,
          selectOption = this.selectOption,
          props = this.props;
      var classNamePrefix = props.classNamePrefix,
          isMulti = props.isMulti,
          isRtl = props.isRtl,
          options = props.options;
      var selectValue = this.state.selectValue;
      var hasValue = this.hasValue();

      var getValue = function getValue() {
        return selectValue;
      };

      var cx = classNames.bind(null, classNamePrefix);
      return {
        cx: cx,
        clearValue: clearValue,
        getStyles: getStyles,
        getValue: getValue,
        hasValue: hasValue,
        isMulti: isMulti,
        isRtl: isRtl,
        options: options,
        selectOption: selectOption,
        setValue: setValue,
        selectProps: props,
        theme: this.getTheme()
      };
    };

    _proto.getNextFocusedValue = function getNextFocusedValue(nextSelectValue) {
      if (this.clearFocusValueOnUpdate) {
        this.clearFocusValueOnUpdate = false;
        return null;
      }

      var _this$state6 = this.state,
          focusedValue = _this$state6.focusedValue,
          lastSelectValue = _this$state6.selectValue;
      var lastFocusedIndex = lastSelectValue.indexOf(focusedValue);

      if (lastFocusedIndex > -1) {
        var nextFocusedIndex = nextSelectValue.indexOf(focusedValue);

        if (nextFocusedIndex > -1) {
          // the focused value is still in the selectValue, return it
          return focusedValue;
        } else if (lastFocusedIndex < nextSelectValue.length) {
          // the focusedValue is not present in the next selectValue array by
          // reference, so return the new value at the same index
          return nextSelectValue[lastFocusedIndex];
        }
      }

      return null;
    };

    _proto.getNextFocusedOption = function getNextFocusedOption(options) {
      var lastFocusedOption = this.state.focusedOption;
      return lastFocusedOption && options.indexOf(lastFocusedOption) > -1 ? lastFocusedOption : options[0];
    };

    _proto.hasValue = function hasValue() {
      var selectValue = this.state.selectValue;
      return selectValue.length > 0;
    };

    _proto.hasOptions = function hasOptions() {
      return !!this.state.menuOptions.render.length;
    };

    _proto.countOptions = function countOptions() {
      return this.state.menuOptions.focusable.length;
    };

    _proto.isClearable = function isClearable() {
      var _this$props12 = this.props,
          isClearable = _this$props12.isClearable,
          isMulti = _this$props12.isMulti; // single select, by default, IS NOT clearable
      // multi select, by default, IS clearable

      if (isClearable === undefined) return isMulti;
      return isClearable;
    };

    _proto.isOptionDisabled = function isOptionDisabled(option, selectValue) {
      return typeof this.props.isOptionDisabled === 'function' ? this.props.isOptionDisabled(option, selectValue) : false;
    };

    _proto.isOptionSelected = function isOptionSelected(option, selectValue) {
      var _this3 = this;

      if (selectValue.indexOf(option) > -1) return true;

      if (typeof this.props.isOptionSelected === 'function') {
        return this.props.isOptionSelected(option, selectValue);
      }

      var candidate = this.getOptionValue(option);
      return selectValue.some(function (i) {
        return _this3.getOptionValue(i) === candidate;
      });
    };

    _proto.filterOption = function filterOption(option, inputValue) {
      return this.props.filterOption ? this.props.filterOption(option, inputValue) : true;
    };

    _proto.formatOptionLabel = function formatOptionLabel(data, context) {
      if (typeof this.props.formatOptionLabel === 'function') {
        var inputValue = this.props.inputValue;
        var selectValue = this.state.selectValue;
        return this.props.formatOptionLabel(data, {
          context: context,
          inputValue: inputValue,
          selectValue: selectValue
        });
      } else {
        return this.getOptionLabel(data);
      }
    };

    _proto.formatGroupLabel = function formatGroupLabel(data) {
      return this.props.formatGroupLabel(data);
    } // ==============================
    // Mouse Handlers
    // ==============================
    ;

    // ==============================
    // Composition Handlers
    // ==============================
    _proto.startListeningComposition = function startListeningComposition() {
      if (document && document.addEventListener) {
        document.addEventListener('compositionstart', this.onCompositionStart, false);
        document.addEventListener('compositionend', this.onCompositionEnd, false);
      }
    };

    _proto.stopListeningComposition = function stopListeningComposition() {
      if (document && document.removeEventListener) {
        document.removeEventListener('compositionstart', this.onCompositionStart);
        document.removeEventListener('compositionend', this.onCompositionEnd);
      }
    };

    // ==============================
    // Touch Handlers
    // ==============================
    _proto.startListeningToTouch = function startListeningToTouch() {
      if (document && document.addEventListener) {
        document.addEventListener('touchstart', this.onTouchStart, false);
        document.addEventListener('touchmove', this.onTouchMove, false);
        document.addEventListener('touchend', this.onTouchEnd, false);
      }
    };

    _proto.stopListeningToTouch = function stopListeningToTouch() {
      if (document && document.removeEventListener) {
        document.removeEventListener('touchstart', this.onTouchStart);
        document.removeEventListener('touchmove', this.onTouchMove);
        document.removeEventListener('touchend', this.onTouchEnd);
      }
    };

    // ==============================
    // Renderers
    // ==============================
    _proto.constructAriaLiveMessage = function constructAriaLiveMessage() {
      var _this$state7 = this.state,
          ariaLiveContext = _this$state7.ariaLiveContext,
          selectValue = _this$state7.selectValue,
          focusedValue = _this$state7.focusedValue,
          focusedOption = _this$state7.focusedOption;
      var _this$props13 = this.props,
          options = _this$props13.options,
          menuIsOpen = _this$props13.menuIsOpen,
          inputValue = _this$props13.inputValue,
          screenReaderStatus = _this$props13.screenReaderStatus; // An aria live message representing the currently focused value in the select.

      var focusedValueMsg = focusedValue ? valueFocusAriaMessage({
        focusedValue: focusedValue,
        getOptionLabel: this.getOptionLabel,
        selectValue: selectValue
      }) : ''; // An aria live message representing the currently focused option in the select.

      var focusedOptionMsg = focusedOption && menuIsOpen ? optionFocusAriaMessage({
        focusedOption: focusedOption,
        getOptionLabel: this.getOptionLabel,
        options: options
      }) : ''; // An aria live message representing the set of focusable results and current searchterm/inputvalue.

      var resultsMsg = resultsAriaMessage({
        inputValue: inputValue,
        screenReaderMessage: screenReaderStatus({
          count: this.countOptions()
        })
      });
      return focusedValueMsg + " " + focusedOptionMsg + " " + resultsMsg + " " + ariaLiveContext;
    };

    _proto.renderInput = function renderInput() {
      var _this$props14 = this.props,
          isDisabled = _this$props14.isDisabled,
          isSearchable = _this$props14.isSearchable,
          inputId = _this$props14.inputId,
          inputValue = _this$props14.inputValue,
          tabIndex = _this$props14.tabIndex;
      var Input = this.components.Input;
      var inputIsHidden = this.state.inputIsHidden;
      var id = inputId || this.getElementId('input'); // aria attributes makes the JSX "noisy", separated for clarity

      var ariaAttributes = {
        'aria-autocomplete': 'list',
        'aria-label': this.props['aria-label'],
        'aria-labelledby': this.props['aria-labelledby']
      };

      if (!isSearchable) {
        // use a dummy input to maintain focus/blur functionality
        return React__default.createElement(DummyInput, _extends$4$1({
          id: id,
          innerRef: this.getInputRef,
          onBlur: this.onInputBlur,
          onChange: noop,
          onFocus: this.onInputFocus,
          readOnly: true,
          disabled: isDisabled,
          tabIndex: tabIndex,
          value: ""
        }, ariaAttributes));
      }

      var _this$commonProps = this.commonProps,
          cx = _this$commonProps.cx,
          theme = _this$commonProps.theme,
          selectProps = _this$commonProps.selectProps;
      return React__default.createElement(Input, _extends$4$1({
        autoCapitalize: "none",
        autoComplete: "off",
        autoCorrect: "off",
        cx: cx,
        getStyles: this.getStyles,
        id: id,
        innerRef: this.getInputRef,
        isDisabled: isDisabled,
        isHidden: inputIsHidden,
        onBlur: this.onInputBlur,
        onChange: this.handleInputChange,
        onFocus: this.onInputFocus,
        selectProps: selectProps,
        spellCheck: "false",
        tabIndex: tabIndex,
        theme: theme,
        type: "text",
        value: inputValue
      }, ariaAttributes));
    };

    _proto.renderPlaceholderOrValue = function renderPlaceholderOrValue() {
      var _this4 = this;

      var _this$components = this.components,
          MultiValue = _this$components.MultiValue,
          MultiValueContainer = _this$components.MultiValueContainer,
          MultiValueLabel = _this$components.MultiValueLabel,
          MultiValueRemove = _this$components.MultiValueRemove,
          SingleValue = _this$components.SingleValue,
          Placeholder = _this$components.Placeholder;
      var commonProps = this.commonProps;
      var _this$props15 = this.props,
          controlShouldRenderValue = _this$props15.controlShouldRenderValue,
          isDisabled = _this$props15.isDisabled,
          isMulti = _this$props15.isMulti,
          inputValue = _this$props15.inputValue,
          placeholder = _this$props15.placeholder;
      var _this$state8 = this.state,
          selectValue = _this$state8.selectValue,
          focusedValue = _this$state8.focusedValue,
          isFocused = _this$state8.isFocused;

      if (!this.hasValue() || !controlShouldRenderValue) {
        return inputValue ? null : React__default.createElement(Placeholder, _extends$4$1({}, commonProps, {
          key: "placeholder",
          isDisabled: isDisabled,
          isFocused: isFocused
        }), placeholder);
      }

      if (isMulti) {
        var selectValues = selectValue.map(function (opt, index) {
          var isOptionFocused = opt === focusedValue;
          return React__default.createElement(MultiValue, _extends$4$1({}, commonProps, {
            components: {
              Container: MultiValueContainer,
              Label: MultiValueLabel,
              Remove: MultiValueRemove
            },
            isFocused: isOptionFocused,
            isDisabled: isDisabled,
            key: _this4.getOptionValue(opt),
            index: index,
            removeProps: {
              onClick: function onClick() {
                return _this4.removeValue(opt);
              },
              onTouchEnd: function onTouchEnd() {
                return _this4.removeValue(opt);
              },
              onMouseDown: function onMouseDown(e) {
                e.preventDefault();
                e.stopPropagation();
              }
            },
            data: opt
          }), _this4.formatOptionLabel(opt, 'value'));
        });
        return selectValues;
      }

      if (inputValue) {
        return null;
      }

      var singleValue = selectValue[0];
      return React__default.createElement(SingleValue, _extends$4$1({}, commonProps, {
        data: singleValue,
        isDisabled: isDisabled
      }), this.formatOptionLabel(singleValue, 'value'));
    };

    _proto.renderClearIndicator = function renderClearIndicator() {
      var ClearIndicator = this.components.ClearIndicator;
      var commonProps = this.commonProps;
      var _this$props16 = this.props,
          isDisabled = _this$props16.isDisabled,
          isLoading = _this$props16.isLoading;
      var isFocused = this.state.isFocused;

      if (!this.isClearable() || !ClearIndicator || isDisabled || !this.hasValue() || isLoading) {
        return null;
      }

      var innerProps = {
        onMouseDown: this.onClearIndicatorMouseDown,
        onTouchEnd: this.onClearIndicatorTouchEnd,
        'aria-hidden': 'true'
      };
      return React__default.createElement(ClearIndicator, _extends$4$1({}, commonProps, {
        innerProps: innerProps,
        isFocused: isFocused
      }));
    };

    _proto.renderLoadingIndicator = function renderLoadingIndicator() {
      var LoadingIndicator = this.components.LoadingIndicator;
      var commonProps = this.commonProps;
      var _this$props17 = this.props,
          isDisabled = _this$props17.isDisabled,
          isLoading = _this$props17.isLoading;
      var isFocused = this.state.isFocused;
      if (!LoadingIndicator || !isLoading) return null;
      var innerProps = {
        'aria-hidden': 'true'
      };
      return React__default.createElement(LoadingIndicator, _extends$4$1({}, commonProps, {
        innerProps: innerProps,
        isDisabled: isDisabled,
        isFocused: isFocused
      }));
    };

    _proto.renderIndicatorSeparator = function renderIndicatorSeparator() {
      var _this$components2 = this.components,
          DropdownIndicator = _this$components2.DropdownIndicator,
          IndicatorSeparator = _this$components2.IndicatorSeparator; // separator doesn't make sense without the dropdown indicator

      if (!DropdownIndicator || !IndicatorSeparator) return null;
      var commonProps = this.commonProps;
      var isDisabled = this.props.isDisabled;
      var isFocused = this.state.isFocused;
      return React__default.createElement(IndicatorSeparator, _extends$4$1({}, commonProps, {
        isDisabled: isDisabled,
        isFocused: isFocused
      }));
    };

    _proto.renderDropdownIndicator = function renderDropdownIndicator() {
      var DropdownIndicator = this.components.DropdownIndicator;
      if (!DropdownIndicator) return null;
      var commonProps = this.commonProps;
      var isDisabled = this.props.isDisabled;
      var isFocused = this.state.isFocused;
      var innerProps = {
        onMouseDown: this.onDropdownIndicatorMouseDown,
        onTouchEnd: this.onDropdownIndicatorTouchEnd,
        'aria-hidden': 'true'
      };
      return React__default.createElement(DropdownIndicator, _extends$4$1({}, commonProps, {
        innerProps: innerProps,
        isDisabled: isDisabled,
        isFocused: isFocused
      }));
    };

    _proto.renderMenu = function renderMenu() {
      var _this5 = this;

      var _this$components3 = this.components,
          Group = _this$components3.Group,
          GroupHeading = _this$components3.GroupHeading,
          Menu = _this$components3.Menu,
          MenuList = _this$components3.MenuList,
          MenuPortal = _this$components3.MenuPortal,
          LoadingMessage = _this$components3.LoadingMessage,
          NoOptionsMessage = _this$components3.NoOptionsMessage,
          Option = _this$components3.Option;
      var commonProps = this.commonProps;
      var _this$state9 = this.state,
          focusedOption = _this$state9.focusedOption,
          menuOptions = _this$state9.menuOptions;
      var _this$props18 = this.props,
          captureMenuScroll = _this$props18.captureMenuScroll,
          inputValue = _this$props18.inputValue,
          isLoading = _this$props18.isLoading,
          loadingMessage = _this$props18.loadingMessage,
          minMenuHeight = _this$props18.minMenuHeight,
          maxMenuHeight = _this$props18.maxMenuHeight,
          menuIsOpen = _this$props18.menuIsOpen,
          menuPlacement = _this$props18.menuPlacement,
          menuPosition = _this$props18.menuPosition,
          menuPortalTarget = _this$props18.menuPortalTarget,
          menuShouldBlockScroll = _this$props18.menuShouldBlockScroll,
          menuShouldScrollIntoView = _this$props18.menuShouldScrollIntoView,
          noOptionsMessage = _this$props18.noOptionsMessage,
          onMenuScrollToTop = _this$props18.onMenuScrollToTop,
          onMenuScrollToBottom = _this$props18.onMenuScrollToBottom;
      if (!menuIsOpen) return null; // TODO: Internal Option Type here

      var render = function render(props) {
        // for performance, the menu options in state aren't changed when the
        // focused option changes so we calculate additional props based on that
        var isFocused = focusedOption === props.data;
        props.innerRef = isFocused ? _this5.getFocusedOptionRef : undefined;
        return React__default.createElement(Option, _extends$4$1({}, commonProps, props, {
          isFocused: isFocused
        }), _this5.formatOptionLabel(props.data, 'menu'));
      };

      var menuUI;

      if (this.hasOptions()) {
        menuUI = menuOptions.render.map(function (item) {
          if (item.type === 'group') {
            var type = item.type,
                group = _objectWithoutPropertiesLoose$2$1(item, ["type"]);

            var headingId = item.key + "-heading";
            return React__default.createElement(Group, _extends$4$1({}, commonProps, group, {
              Heading: GroupHeading,
              headingProps: {
                id: headingId
              },
              label: _this5.formatGroupLabel(item.data)
            }), item.options.map(function (option) {
              return render(option);
            }));
          } else if (item.type === 'option') {
            return render(item);
          }
        });
      } else if (isLoading) {
        var message = loadingMessage({
          inputValue: inputValue
        });
        if (message === null) return null;
        menuUI = React__default.createElement(LoadingMessage, commonProps, message);
      } else {
        var _message = noOptionsMessage({
          inputValue: inputValue
        });

        if (_message === null) return null;
        menuUI = React__default.createElement(NoOptionsMessage, commonProps, _message);
      }

      var menuPlacementProps = {
        minMenuHeight: minMenuHeight,
        maxMenuHeight: maxMenuHeight,
        menuPlacement: menuPlacement,
        menuPosition: menuPosition,
        menuShouldScrollIntoView: menuShouldScrollIntoView
      };
      var menuElement = React__default.createElement(MenuPlacer, _extends$4$1({}, commonProps, menuPlacementProps), function (_ref8) {
        var ref = _ref8.ref,
            _ref8$placerProps = _ref8.placerProps,
            placement = _ref8$placerProps.placement,
            maxHeight = _ref8$placerProps.maxHeight;
        return React__default.createElement(Menu, _extends$4$1({}, commonProps, menuPlacementProps, {
          innerRef: ref,
          innerProps: {
            onMouseDown: _this5.onMenuMouseDown,
            onMouseMove: _this5.onMenuMouseMove
          },
          isLoading: isLoading,
          placement: placement
        }), React__default.createElement(ScrollCaptorSwitch, {
          isEnabled: captureMenuScroll,
          onTopArrive: onMenuScrollToTop,
          onBottomArrive: onMenuScrollToBottom
        }, React__default.createElement(ScrollBlock, {
          isEnabled: menuShouldBlockScroll
        }, React__default.createElement(MenuList, _extends$4$1({}, commonProps, {
          innerRef: _this5.getMenuListRef,
          isLoading: isLoading,
          maxHeight: maxHeight
        }), menuUI))));
      }); // positioning behaviour is almost identical for portalled and fixed,
      // so we use the same component. the actual portalling logic is forked
      // within the component based on `menuPosition`

      return menuPortalTarget || menuPosition === 'fixed' ? React__default.createElement(MenuPortal, _extends$4$1({}, commonProps, {
        appendTo: menuPortalTarget,
        controlElement: this.controlRef,
        menuPlacement: menuPlacement,
        menuPosition: menuPosition
      }), menuElement) : menuElement;
    };

    _proto.renderFormField = function renderFormField() {
      var _this6 = this;

      var _this$props19 = this.props,
          delimiter = _this$props19.delimiter,
          isDisabled = _this$props19.isDisabled,
          isMulti = _this$props19.isMulti,
          name = _this$props19.name;
      var selectValue = this.state.selectValue;
      if (!name || isDisabled) return;

      if (isMulti) {
        if (delimiter) {
          var value = selectValue.map(function (opt) {
            return _this6.getOptionValue(opt);
          }).join(delimiter);
          return React__default.createElement("input", {
            name: name,
            type: "hidden",
            value: value
          });
        } else {
          var input = selectValue.length > 0 ? selectValue.map(function (opt, i) {
            return React__default.createElement("input", {
              key: "i-" + i,
              name: name,
              type: "hidden",
              value: _this6.getOptionValue(opt)
            });
          }) : React__default.createElement("input", {
            name: name,
            type: "hidden"
          });
          return React__default.createElement("div", null, input);
        }
      } else {
        var _value2 = selectValue[0] ? this.getOptionValue(selectValue[0]) : '';

        return React__default.createElement("input", {
          name: name,
          type: "hidden",
          value: _value2
        });
      }
    };

    _proto.renderLiveRegion = function renderLiveRegion() {
      if (!this.state.isFocused) return null;
      return React__default.createElement(A11yText, {
        "aria-live": "polite"
      }, React__default.createElement("p", {
        id: "aria-selection-event"
      }, "\xA0", this.state.ariaLiveSelection), React__default.createElement("p", {
        id: "aria-context"
      }, "\xA0", this.constructAriaLiveMessage()));
    };

    _proto.render = function render() {
      var _this$components4 = this.components,
          Control = _this$components4.Control,
          IndicatorsContainer = _this$components4.IndicatorsContainer,
          SelectContainer = _this$components4.SelectContainer,
          ValueContainer = _this$components4.ValueContainer;
      var _this$props20 = this.props,
          className = _this$props20.className,
          id = _this$props20.id,
          isDisabled = _this$props20.isDisabled,
          menuIsOpen = _this$props20.menuIsOpen;
      var isFocused = this.state.isFocused;
      var commonProps = this.commonProps = this.getCommonProps();
      return React__default.createElement(SelectContainer, _extends$4$1({}, commonProps, {
        className: className,
        innerProps: {
          id: id,
          onKeyDown: this.onKeyDown
        },
        isDisabled: isDisabled,
        isFocused: isFocused
      }), this.renderLiveRegion(), React__default.createElement(Control, _extends$4$1({}, commonProps, {
        innerRef: this.getControlRef,
        innerProps: {
          onMouseDown: this.onControlMouseDown,
          onTouchEnd: this.onControlTouchEnd
        },
        isDisabled: isDisabled,
        isFocused: isFocused,
        menuIsOpen: menuIsOpen
      }), React__default.createElement(ValueContainer, _extends$4$1({}, commonProps, {
        isDisabled: isDisabled
      }), this.renderPlaceholderOrValue(), this.renderInput()), React__default.createElement(IndicatorsContainer, _extends$4$1({}, commonProps, {
        isDisabled: isDisabled
      }), this.renderClearIndicator(), this.renderLoadingIndicator(), this.renderIndicatorSeparator(), this.renderDropdownIndicator())), this.renderMenu(), this.renderFormField());
    };

    return Select;
  }(React.Component);

  Select.defaultProps = defaultProps;

  function _extends$c() { _extends$c = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; }; return _extends$c.apply(this, arguments); }

  function _objectWithoutPropertiesLoose$4(source, excluded) { if (source == null) return {}; var target = {}; var sourceKeys = Object.keys(source); var key, i; for (i = 0; i < sourceKeys.length; i++) { key = sourceKeys[i]; if (excluded.indexOf(key) >= 0) continue; target[key] = source[key]; } return target; }

  function _inheritsLoose$5(subClass, superClass) { subClass.prototype = Object.create(superClass.prototype); subClass.prototype.constructor = subClass; subClass.__proto__ = superClass; }
  var defaultProps$1 = {
    defaultInputValue: '',
    defaultMenuIsOpen: false,
    defaultValue: null
  };

  var manageState = function manageState(SelectComponent) {
    var _class, _temp;

    return _temp = _class =
    /*#__PURE__*/
    function (_Component) {
      _inheritsLoose$5(StateManager, _Component);

      function StateManager() {
        var _this;

        for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
          args[_key] = arguments[_key];
        }

        _this = _Component.call.apply(_Component, [this].concat(args)) || this;
        _this.select = void 0;
        _this.state = {
          inputValue: _this.props.inputValue !== undefined ? _this.props.inputValue : _this.props.defaultInputValue,
          menuIsOpen: _this.props.menuIsOpen !== undefined ? _this.props.menuIsOpen : _this.props.defaultMenuIsOpen,
          value: _this.props.value !== undefined ? _this.props.value : _this.props.defaultValue
        };

        _this.onChange = function (value, actionMeta) {
          _this.callProp('onChange', value, actionMeta);

          _this.setState({
            value: value
          });
        };

        _this.onInputChange = function (value, actionMeta) {
          // TODO: for backwards compatibility, we allow the prop to return a new
          // value, but now inputValue is a controllable prop we probably shouldn't
          var newValue = _this.callProp('onInputChange', value, actionMeta);

          _this.setState({
            inputValue: newValue !== undefined ? newValue : value
          });
        };

        _this.onMenuOpen = function () {
          _this.callProp('onMenuOpen');

          _this.setState({
            menuIsOpen: true
          });
        };

        _this.onMenuClose = function () {
          _this.callProp('onMenuClose');

          _this.setState({
            menuIsOpen: false
          });
        };

        return _this;
      }

      var _proto = StateManager.prototype;

      _proto.focus = function focus() {
        this.select.focus();
      };

      _proto.blur = function blur() {
        this.select.blur();
      } // FIXME: untyped flow code, return any
      ;

      _proto.getProp = function getProp(key) {
        return this.props[key] !== undefined ? this.props[key] : this.state[key];
      } // FIXME: untyped flow code, return any
      ;

      _proto.callProp = function callProp(name) {
        if (typeof this.props[name] === 'function') {
          var _this$props;

          for (var _len2 = arguments.length, args = new Array(_len2 > 1 ? _len2 - 1 : 0), _key2 = 1; _key2 < _len2; _key2++) {
            args[_key2 - 1] = arguments[_key2];
          }

          return (_this$props = this.props)[name].apply(_this$props, args);
        }
      };

      _proto.render = function render() {
        var _this2 = this;

        var _this$props2 = this.props,
            defaultInputValue = _this$props2.defaultInputValue,
            defaultMenuIsOpen = _this$props2.defaultMenuIsOpen,
            defaultValue = _this$props2.defaultValue,
            props = _objectWithoutPropertiesLoose$4(_this$props2, ["defaultInputValue", "defaultMenuIsOpen", "defaultValue"]);

        return React__default.createElement(SelectComponent, _extends$c({}, props, {
          ref: function ref(_ref) {
            _this2.select = _ref;
          },
          inputValue: this.getProp('inputValue'),
          menuIsOpen: this.getProp('menuIsOpen'),
          onChange: this.onChange,
          onInputChange: this.onInputChange,
          onMenuClose: this.onMenuClose,
          onMenuOpen: this.onMenuOpen,
          value: this.getProp('value')
        }));
      };

      return StateManager;
    }(React.Component), _class.defaultProps = defaultProps$1, _temp;
  };

  var index = manageState(Select);

  var countries = [{
    "id": "1",
    "sortname": "AF",
    "name": "Afghanistan",
    "phonecode": "93"
  }, {
    "id": "2",
    "sortname": "AL",
    "name": "Albania",
    "phonecode": "355"
  }, {
    "id": "3",
    "sortname": "DZ",
    "name": "Algeria",
    "phonecode": "213"
  }, {
    "id": "4",
    "sortname": "AS",
    "name": "American Samoa",
    "phonecode": "1684"
  }, {
    "id": "5",
    "sortname": "AD",
    "name": "Andorra",
    "phonecode": "376"
  }, {
    "id": "6",
    "sortname": "AO",
    "name": "Angola",
    "phonecode": "244"
  }, {
    "id": "7",
    "sortname": "AI",
    "name": "Anguilla",
    "phonecode": "1264"
  }, {
    "id": "8",
    "sortname": "AQ",
    "name": "Antarctica",
    "phonecode": "0"
  }, {
    "id": "9",
    "sortname": "AG",
    "name": "Antigua And Barbuda",
    "phonecode": "1268"
  }, {
    "id": "10",
    "sortname": "AR",
    "name": "Argentina",
    "phonecode": "54"
  }, {
    "id": "11",
    "sortname": "AM",
    "name": "Armenia",
    "phonecode": "374"
  }, {
    "id": "12",
    "sortname": "AW",
    "name": "Aruba",
    "phonecode": "297"
  }, {
    "id": "13",
    "sortname": "AU",
    "name": "Australia",
    "phonecode": "61"
  }, {
    "id": "14",
    "sortname": "AT",
    "name": "Austria",
    "phonecode": "43"
  }, {
    "id": "15",
    "sortname": "AZ",
    "name": "Azerbaijan",
    "phonecode": "994"
  }, {
    "id": "16",
    "sortname": "BS",
    "name": "Bahamas The",
    "phonecode": "1242"
  }, {
    "id": "17",
    "sortname": "BH",
    "name": "Bahrain",
    "phonecode": "973"
  }, {
    "id": "18",
    "sortname": "BD",
    "name": "Bangladesh",
    "phonecode": "880"
  }, {
    "id": "19",
    "sortname": "BB",
    "name": "Barbados",
    "phonecode": "1246"
  }, {
    "id": "20",
    "sortname": "BY",
    "name": "Belarus",
    "phonecode": "375"
  }, {
    "id": "21",
    "sortname": "BE",
    "name": "Belgium",
    "phonecode": "32"
  }, {
    "id": "22",
    "sortname": "BZ",
    "name": "Belize",
    "phonecode": "501"
  }, {
    "id": "23",
    "sortname": "BJ",
    "name": "Benin",
    "phonecode": "229"
  }, {
    "id": "24",
    "sortname": "BM",
    "name": "Bermuda",
    "phonecode": "1441"
  }, {
    "id": "25",
    "sortname": "BT",
    "name": "Bhutan",
    "phonecode": "975"
  }, {
    "id": "26",
    "sortname": "BO",
    "name": "Bolivia",
    "phonecode": "591"
  }, {
    "id": "27",
    "sortname": "BA",
    "name": "Bosnia and Herzegovina",
    "phonecode": "387"
  }, {
    "id": "28",
    "sortname": "BW",
    "name": "Botswana",
    "phonecode": "267"
  }, {
    "id": "29",
    "sortname": "BV",
    "name": "Bouvet Island",
    "phonecode": "0"
  }, {
    "id": "30",
    "sortname": "BR",
    "name": "Brazil",
    "phonecode": "55"
  }, {
    "id": "31",
    "sortname": "IO",
    "name": "British Indian Ocean Territory",
    "phonecode": "246"
  }, {
    "id": "32",
    "sortname": "BN",
    "name": "Brunei",
    "phonecode": "673"
  }, {
    "id": "33",
    "sortname": "BG",
    "name": "Bulgaria",
    "phonecode": "359"
  }, {
    "id": "34",
    "sortname": "BF",
    "name": "Burkina Faso",
    "phonecode": "226"
  }, {
    "id": "35",
    "sortname": "BI",
    "name": "Burundi",
    "phonecode": "257"
  }, {
    "id": "36",
    "sortname": "KH",
    "name": "Cambodia",
    "phonecode": "855"
  }, {
    "id": "37",
    "sortname": "CM",
    "name": "Cameroon",
    "phonecode": "237"
  }, {
    "id": "38",
    "sortname": "CA",
    "name": "Canada",
    "phonecode": "1"
  }, {
    "id": "39",
    "sortname": "CV",
    "name": "Cape Verde",
    "phonecode": "238"
  }, {
    "id": "40",
    "sortname": "KY",
    "name": "Cayman Islands",
    "phonecode": "1345"
  }, {
    "id": "41",
    "sortname": "CF",
    "name": "Central African Republic",
    "phonecode": "236"
  }, {
    "id": "42",
    "sortname": "TD",
    "name": "Chad",
    "phonecode": "235"
  }, {
    "id": "43",
    "sortname": "CL",
    "name": "Chile",
    "phonecode": "56"
  }, {
    "id": "44",
    "sortname": "CN",
    "name": "China",
    "phonecode": "86"
  }, {
    "id": "45",
    "sortname": "CX",
    "name": "Christmas Island",
    "phonecode": "61"
  }, {
    "id": "46",
    "sortname": "CC",
    "name": "Cocos (Keeling) Islands",
    "phonecode": "672"
  }, {
    "id": "47",
    "sortname": "CO",
    "name": "Colombia",
    "phonecode": "57"
  }, {
    "id": "48",
    "sortname": "KM",
    "name": "Comoros",
    "phonecode": "269"
  }, {
    "id": "49",
    "sortname": "CG",
    "name": "Republic Of The Congo",
    "phonecode": "242"
  }, {
    "id": "50",
    "sortname": "CD",
    "name": "Democratic Republic Of The Congo",
    "phonecode": "242"
  }, {
    "id": "51",
    "sortname": "CK",
    "name": "Cook Islands",
    "phonecode": "682"
  }, {
    "id": "52",
    "sortname": "CR",
    "name": "Costa Rica",
    "phonecode": "506"
  }, {
    "id": "53",
    "sortname": "CI",
    "name": "Cote D'Ivoire (Ivory Coast)",
    "phonecode": "225"
  }, {
    "id": "54",
    "sortname": "HR",
    "name": "Croatia (Hrvatska)",
    "phonecode": "385"
  }, {
    "id": "55",
    "sortname": "CU",
    "name": "Cuba",
    "phonecode": "53"
  }, {
    "id": "56",
    "sortname": "CY",
    "name": "Cyprus",
    "phonecode": "357"
  }, {
    "id": "57",
    "sortname": "CZ",
    "name": "Czech Republic",
    "phonecode": "420"
  }, {
    "id": "58",
    "sortname": "DK",
    "name": "Denmark",
    "phonecode": "45"
  }, {
    "id": "59",
    "sortname": "DJ",
    "name": "Djibouti",
    "phonecode": "253"
  }, {
    "id": "60",
    "sortname": "DM",
    "name": "Dominica",
    "phonecode": "1767"
  }, {
    "id": "61",
    "sortname": "DO",
    "name": "Dominican Republic",
    "phonecode": "1809"
  }, {
    "id": "62",
    "sortname": "TP",
    "name": "East Timor",
    "phonecode": "670"
  }, {
    "id": "63",
    "sortname": "EC",
    "name": "Ecuador",
    "phonecode": "593"
  }, {
    "id": "64",
    "sortname": "EG",
    "name": "Egypt",
    "phonecode": "20"
  }, {
    "id": "65",
    "sortname": "SV",
    "name": "El Salvador",
    "phonecode": "503"
  }, {
    "id": "66",
    "sortname": "GQ",
    "name": "Equatorial Guinea",
    "phonecode": "240"
  }, {
    "id": "67",
    "sortname": "ER",
    "name": "Eritrea",
    "phonecode": "291"
  }, {
    "id": "68",
    "sortname": "EE",
    "name": "Estonia",
    "phonecode": "372"
  }, {
    "id": "69",
    "sortname": "ET",
    "name": "Ethiopia",
    "phonecode": "251"
  }, {
    "id": "70",
    "sortname": "XA",
    "name": "External Territories of Australia",
    "phonecode": "61"
  }, {
    "id": "71",
    "sortname": "FK",
    "name": "Falkland Islands",
    "phonecode": "500"
  }, {
    "id": "72",
    "sortname": "FO",
    "name": "Faroe Islands",
    "phonecode": "298"
  }, {
    "id": "73",
    "sortname": "FJ",
    "name": "Fiji Islands",
    "phonecode": "679"
  }, {
    "id": "74",
    "sortname": "FI",
    "name": "Finland",
    "phonecode": "358"
  }, {
    "id": "75",
    "sortname": "FR",
    "name": "France",
    "phonecode": "33"
  }, {
    "id": "76",
    "sortname": "GF",
    "name": "French Guiana",
    "phonecode": "594"
  }, {
    "id": "77",
    "sortname": "PF",
    "name": "French Polynesia",
    "phonecode": "689"
  }, {
    "id": "78",
    "sortname": "TF",
    "name": "French Southern Territories",
    "phonecode": "0"
  }, {
    "id": "79",
    "sortname": "GA",
    "name": "Gabon",
    "phonecode": "241"
  }, {
    "id": "80",
    "sortname": "GM",
    "name": "Gambia The",
    "phonecode": "220"
  }, {
    "id": "81",
    "sortname": "GE",
    "name": "Georgia",
    "phonecode": "995"
  }, {
    "id": "82",
    "sortname": "DE",
    "name": "Germany",
    "phonecode": "49"
  }, {
    "id": "83",
    "sortname": "GH",
    "name": "Ghana",
    "phonecode": "233"
  }, {
    "id": "84",
    "sortname": "GI",
    "name": "Gibraltar",
    "phonecode": "350"
  }, {
    "id": "85",
    "sortname": "GR",
    "name": "Greece",
    "phonecode": "30"
  }, {
    "id": "86",
    "sortname": "GL",
    "name": "Greenland",
    "phonecode": "299"
  }, {
    "id": "87",
    "sortname": "GD",
    "name": "Grenada",
    "phonecode": "1473"
  }, {
    "id": "88",
    "sortname": "GP",
    "name": "Guadeloupe",
    "phonecode": "590"
  }, {
    "id": "89",
    "sortname": "GU",
    "name": "Guam",
    "phonecode": "1671"
  }, {
    "id": "90",
    "sortname": "GT",
    "name": "Guatemala",
    "phonecode": "502"
  }, {
    "id": "91",
    "sortname": "XU",
    "name": "Guernsey and Alderney",
    "phonecode": "44"
  }, {
    "id": "92",
    "sortname": "GN",
    "name": "Guinea",
    "phonecode": "224"
  }, {
    "id": "93",
    "sortname": "GW",
    "name": "Guinea-Bissau",
    "phonecode": "245"
  }, {
    "id": "94",
    "sortname": "GY",
    "name": "Guyana",
    "phonecode": "592"
  }, {
    "id": "95",
    "sortname": "HT",
    "name": "Haiti",
    "phonecode": "509"
  }, {
    "id": "96",
    "sortname": "HM",
    "name": "Heard and McDonald Islands",
    "phonecode": "0"
  }, {
    "id": "97",
    "sortname": "HN",
    "name": "Honduras",
    "phonecode": "504"
  }, {
    "id": "98",
    "sortname": "HK",
    "name": "Hong Kong S.A.R.",
    "phonecode": "852"
  }, {
    "id": "99",
    "sortname": "HU",
    "name": "Hungary",
    "phonecode": "36"
  }, {
    "id": "100",
    "sortname": "IS",
    "name": "Iceland",
    "phonecode": "354"
  }, {
    "id": "101",
    "sortname": "IN",
    "name": "India",
    "phonecode": "91"
  }, {
    "id": "102",
    "sortname": "ID",
    "name": "Indonesia",
    "phonecode": "62"
  }, {
    "id": "103",
    "sortname": "IR",
    "name": "Iran",
    "phonecode": "98"
  }, {
    "id": "104",
    "sortname": "IQ",
    "name": "Iraq",
    "phonecode": "964"
  }, {
    "id": "105",
    "sortname": "IE",
    "name": "Ireland",
    "phonecode": "353"
  }, {
    "id": "106",
    "sortname": "IL",
    "name": "Israel",
    "phonecode": "972"
  }, {
    "id": "107",
    "sortname": "IT",
    "name": "Italy",
    "phonecode": "39"
  }, {
    "id": "108",
    "sortname": "JM",
    "name": "Jamaica",
    "phonecode": "1876"
  }, {
    "id": "109",
    "sortname": "JP",
    "name": "Japan",
    "phonecode": "81"
  }, {
    "id": "110",
    "sortname": "XJ",
    "name": "Jersey",
    "phonecode": "44"
  }, {
    "id": "111",
    "sortname": "JO",
    "name": "Jordan",
    "phonecode": "962"
  }, {
    "id": "112",
    "sortname": "KZ",
    "name": "Kazakhstan",
    "phonecode": "7"
  }, {
    "id": "113",
    "sortname": "KE",
    "name": "Kenya",
    "phonecode": "254"
  }, {
    "id": "114",
    "sortname": "KI",
    "name": "Kiribati",
    "phonecode": "686"
  }, {
    "id": "115",
    "sortname": "KP",
    "name": "Korea North",
    "phonecode": "850"
  }, {
    "id": "116",
    "sortname": "KR",
    "name": "Korea South",
    "phonecode": "82"
  }, {
    "id": "117",
    "sortname": "KW",
    "name": "Kuwait",
    "phonecode": "965"
  }, {
    "id": "118",
    "sortname": "KG",
    "name": "Kyrgyzstan",
    "phonecode": "996"
  }, {
    "id": "119",
    "sortname": "LA",
    "name": "Laos",
    "phonecode": "856"
  }, {
    "id": "120",
    "sortname": "LV",
    "name": "Latvia",
    "phonecode": "371"
  }, {
    "id": "121",
    "sortname": "LB",
    "name": "Lebanon",
    "phonecode": "961"
  }, {
    "id": "122",
    "sortname": "LS",
    "name": "Lesotho",
    "phonecode": "266"
  }, {
    "id": "123",
    "sortname": "LR",
    "name": "Liberia",
    "phonecode": "231"
  }, {
    "id": "124",
    "sortname": "LY",
    "name": "Libya",
    "phonecode": "218"
  }, {
    "id": "125",
    "sortname": "LI",
    "name": "Liechtenstein",
    "phonecode": "423"
  }, {
    "id": "126",
    "sortname": "LT",
    "name": "Lithuania",
    "phonecode": "370"
  }, {
    "id": "127",
    "sortname": "LU",
    "name": "Luxembourg",
    "phonecode": "352"
  }, {
    "id": "128",
    "sortname": "MO",
    "name": "Macau S.A.R.",
    "phonecode": "853"
  }, {
    "id": "129",
    "sortname": "MK",
    "name": "Macedonia",
    "phonecode": "389"
  }, {
    "id": "130",
    "sortname": "MG",
    "name": "Madagascar",
    "phonecode": "261"
  }, {
    "id": "131",
    "sortname": "MW",
    "name": "Malawi",
    "phonecode": "265"
  }, {
    "id": "132",
    "sortname": "MY",
    "name": "Malaysia",
    "phonecode": "60"
  }, {
    "id": "133",
    "sortname": "MV",
    "name": "Maldives",
    "phonecode": "960"
  }, {
    "id": "134",
    "sortname": "ML",
    "name": "Mali",
    "phonecode": "223"
  }, {
    "id": "135",
    "sortname": "MT",
    "name": "Malta",
    "phonecode": "356"
  }, {
    "id": "136",
    "sortname": "XM",
    "name": "Man (Isle of)",
    "phonecode": "44"
  }, {
    "id": "137",
    "sortname": "MH",
    "name": "Marshall Islands",
    "phonecode": "692"
  }, {
    "id": "138",
    "sortname": "MQ",
    "name": "Martinique",
    "phonecode": "596"
  }, {
    "id": "139",
    "sortname": "MR",
    "name": "Mauritania",
    "phonecode": "222"
  }, {
    "id": "140",
    "sortname": "MU",
    "name": "Mauritius",
    "phonecode": "230"
  }, {
    "id": "141",
    "sortname": "YT",
    "name": "Mayotte",
    "phonecode": "269"
  }, {
    "id": "142",
    "sortname": "MX",
    "name": "Mexico",
    "phonecode": "52"
  }, {
    "id": "143",
    "sortname": "FM",
    "name": "Micronesia",
    "phonecode": "691"
  }, {
    "id": "144",
    "sortname": "MD",
    "name": "Moldova",
    "phonecode": "373"
  }, {
    "id": "145",
    "sortname": "MC",
    "name": "Monaco",
    "phonecode": "377"
  }, {
    "id": "146",
    "sortname": "MN",
    "name": "Mongolia",
    "phonecode": "976"
  }, {
    "id": "147",
    "sortname": "MS",
    "name": "Montserrat",
    "phonecode": "1664"
  }, {
    "id": "148",
    "sortname": "MA",
    "name": "Morocco",
    "phonecode": "212"
  }, {
    "id": "149",
    "sortname": "MZ",
    "name": "Mozambique",
    "phonecode": "258"
  }, {
    "id": "150",
    "sortname": "MM",
    "name": "Myanmar",
    "phonecode": "95"
  }, {
    "id": "151",
    "sortname": "NA",
    "name": "Namibia",
    "phonecode": "264"
  }, {
    "id": "152",
    "sortname": "NR",
    "name": "Nauru",
    "phonecode": "674"
  }, {
    "id": "153",
    "sortname": "NP",
    "name": "Nepal",
    "phonecode": "977"
  }, {
    "id": "154",
    "sortname": "AN",
    "name": "Netherlands Antilles",
    "phonecode": "599"
  }, {
    "id": "155",
    "sortname": "NL",
    "name": "Netherlands The",
    "phonecode": "31"
  }, {
    "id": "156",
    "sortname": "NC",
    "name": "New Caledonia",
    "phonecode": "687"
  }, {
    "id": "157",
    "sortname": "NZ",
    "name": "New Zealand",
    "phonecode": "64"
  }, {
    "id": "158",
    "sortname": "NI",
    "name": "Nicaragua",
    "phonecode": "505"
  }, {
    "id": "159",
    "sortname": "NE",
    "name": "Niger",
    "phonecode": "227"
  }, {
    "id": "160",
    "sortname": "NG",
    "name": "Nigeria",
    "phonecode": "234"
  }, {
    "id": "161",
    "sortname": "NU",
    "name": "Niue",
    "phonecode": "683"
  }, {
    "id": "162",
    "sortname": "NF",
    "name": "Norfolk Island",
    "phonecode": "672"
  }, {
    "id": "163",
    "sortname": "MP",
    "name": "Northern Mariana Islands",
    "phonecode": "1670"
  }, {
    "id": "164",
    "sortname": "NO",
    "name": "Norway",
    "phonecode": "47"
  }, {
    "id": "165",
    "sortname": "OM",
    "name": "Oman",
    "phonecode": "968"
  }, {
    "id": "166",
    "sortname": "PK",
    "name": "Pakistan",
    "phonecode": "92"
  }, {
    "id": "167",
    "sortname": "PW",
    "name": "Palau",
    "phonecode": "680"
  }, {
    "id": "168",
    "sortname": "PS",
    "name": "Palestinian Territory Occupied",
    "phonecode": "970"
  }, {
    "id": "169",
    "sortname": "PA",
    "name": "Panama",
    "phonecode": "507"
  }, {
    "id": "170",
    "sortname": "PG",
    "name": "Papua new Guinea",
    "phonecode": "675"
  }, {
    "id": "171",
    "sortname": "PY",
    "name": "Paraguay",
    "phonecode": "595"
  }, {
    "id": "172",
    "sortname": "PE",
    "name": "Peru",
    "phonecode": "51"
  }, {
    "id": "173",
    "sortname": "PH",
    "name": "Philippines",
    "phonecode": "63"
  }, {
    "id": "174",
    "sortname": "PN",
    "name": "Pitcairn Island",
    "phonecode": "0"
  }, {
    "id": "175",
    "sortname": "PL",
    "name": "Poland",
    "phonecode": "48"
  }, {
    "id": "176",
    "sortname": "PT",
    "name": "Portugal",
    "phonecode": "351"
  }, {
    "id": "177",
    "sortname": "PR",
    "name": "Puerto Rico",
    "phonecode": "1787"
  }, {
    "id": "178",
    "sortname": "QA",
    "name": "Qatar",
    "phonecode": "974"
  }, {
    "id": "179",
    "sortname": "RE",
    "name": "Reunion",
    "phonecode": "262"
  }, {
    "id": "180",
    "sortname": "RO",
    "name": "Romania",
    "phonecode": "40"
  }, {
    "id": "181",
    "sortname": "RU",
    "name": "Russia",
    "phonecode": "70"
  }, {
    "id": "182",
    "sortname": "RW",
    "name": "Rwanda",
    "phonecode": "250"
  }, {
    "id": "183",
    "sortname": "SH",
    "name": "Saint Helena",
    "phonecode": "290"
  }, {
    "id": "184",
    "sortname": "KN",
    "name": "Saint Kitts And Nevis",
    "phonecode": "1869"
  }, {
    "id": "185",
    "sortname": "LC",
    "name": "Saint Lucia",
    "phonecode": "1758"
  }, {
    "id": "186",
    "sortname": "PM",
    "name": "Saint Pierre and Miquelon",
    "phonecode": "508"
  }, {
    "id": "187",
    "sortname": "VC",
    "name": "Saint Vincent And The Grenadines",
    "phonecode": "1784"
  }, {
    "id": "188",
    "sortname": "WS",
    "name": "Samoa",
    "phonecode": "684"
  }, {
    "id": "189",
    "sortname": "SM",
    "name": "San Marino",
    "phonecode": "378"
  }, {
    "id": "190",
    "sortname": "ST",
    "name": "Sao Tome and Principe",
    "phonecode": "239"
  }, {
    "id": "191",
    "sortname": "SA",
    "name": "Saudi Arabia",
    "phonecode": "966"
  }, {
    "id": "192",
    "sortname": "SN",
    "name": "Senegal",
    "phonecode": "221"
  }, {
    "id": "193",
    "sortname": "RS",
    "name": "Serbia",
    "phonecode": "381"
  }, {
    "id": "194",
    "sortname": "SC",
    "name": "Seychelles",
    "phonecode": "248"
  }, {
    "id": "195",
    "sortname": "SL",
    "name": "Sierra Leone",
    "phonecode": "232"
  }, {
    "id": "196",
    "sortname": "SG",
    "name": "Singapore",
    "phonecode": "65"
  }, {
    "id": "197",
    "sortname": "SK",
    "name": "Slovakia",
    "phonecode": "421"
  }, {
    "id": "198",
    "sortname": "SI",
    "name": "Slovenia",
    "phonecode": "386"
  }, {
    "id": "199",
    "sortname": "XG",
    "name": "Smaller Territories of the UK",
    "phonecode": "44"
  }, {
    "id": "200",
    "sortname": "SB",
    "name": "Solomon Islands",
    "phonecode": "677"
  }, {
    "id": "201",
    "sortname": "SO",
    "name": "Somalia",
    "phonecode": "252"
  }, {
    "id": "202",
    "sortname": "ZA",
    "name": "South Africa",
    "phonecode": "27"
  }, {
    "id": "203",
    "sortname": "GS",
    "name": "South Georgia",
    "phonecode": "0"
  }, {
    "id": "204",
    "sortname": "SS",
    "name": "South Sudan",
    "phonecode": "211"
  }, {
    "id": "205",
    "sortname": "ES",
    "name": "Spain",
    "phonecode": "34"
  }, {
    "id": "206",
    "sortname": "LK",
    "name": "Sri Lanka",
    "phonecode": "94"
  }, {
    "id": "207",
    "sortname": "SD",
    "name": "Sudan",
    "phonecode": "249"
  }, {
    "id": "208",
    "sortname": "SR",
    "name": "Suriname",
    "phonecode": "597"
  }, {
    "id": "209",
    "sortname": "SJ",
    "name": "Svalbard And Jan Mayen Islands",
    "phonecode": "47"
  }, {
    "id": "210",
    "sortname": "SZ",
    "name": "Swaziland",
    "phonecode": "268"
  }, {
    "id": "211",
    "sortname": "SE",
    "name": "Sweden",
    "phonecode": "46"
  }, {
    "id": "212",
    "sortname": "CH",
    "name": "Switzerland",
    "phonecode": "41"
  }, {
    "id": "213",
    "sortname": "SY",
    "name": "Syria",
    "phonecode": "963"
  }, {
    "id": "214",
    "sortname": "TW",
    "name": "Taiwan",
    "phonecode": "886"
  }, {
    "id": "215",
    "sortname": "TJ",
    "name": "Tajikistan",
    "phonecode": "992"
  }, {
    "id": "216",
    "sortname": "TZ",
    "name": "Tanzania",
    "phonecode": "255"
  }, {
    "id": "217",
    "sortname": "TH",
    "name": "Thailand",
    "phonecode": "66"
  }, {
    "id": "218",
    "sortname": "TG",
    "name": "Togo",
    "phonecode": "228"
  }, {
    "id": "219",
    "sortname": "TK",
    "name": "Tokelau",
    "phonecode": "690"
  }, {
    "id": "220",
    "sortname": "TO",
    "name": "Tonga",
    "phonecode": "676"
  }, {
    "id": "221",
    "sortname": "TT",
    "name": "Trinidad And Tobago",
    "phonecode": "1868"
  }, {
    "id": "222",
    "sortname": "TN",
    "name": "Tunisia",
    "phonecode": "216"
  }, {
    "id": "223",
    "sortname": "TR",
    "name": "Turkey",
    "phonecode": "90"
  }, {
    "id": "224",
    "sortname": "TM",
    "name": "Turkmenistan",
    "phonecode": "7370"
  }, {
    "id": "225",
    "sortname": "TC",
    "name": "Turks And Caicos Islands",
    "phonecode": "1649"
  }, {
    "id": "226",
    "sortname": "TV",
    "name": "Tuvalu",
    "phonecode": "688"
  }, {
    "id": "227",
    "sortname": "UG",
    "name": "Uganda",
    "phonecode": "256"
  }, {
    "id": "228",
    "sortname": "UA",
    "name": "Ukraine",
    "phonecode": "380"
  }, {
    "id": "229",
    "sortname": "AE",
    "name": "United Arab Emirates",
    "phonecode": "971"
  }, {
    "id": "230",
    "sortname": "GB",
    "name": "United Kingdom",
    "phonecode": "44"
  }, {
    "id": "231",
    "sortname": "US",
    "name": "United States",
    "phonecode": "1"
  }, {
    "id": "232",
    "sortname": "UM",
    "name": "United States Minor Outlying Islands",
    "phonecode": "1"
  }, {
    "id": "233",
    "sortname": "UY",
    "name": "Uruguay",
    "phonecode": "598"
  }, {
    "id": "234",
    "sortname": "UZ",
    "name": "Uzbekistan",
    "phonecode": "998"
  }, {
    "id": "235",
    "sortname": "VU",
    "name": "Vanuatu",
    "phonecode": "678"
  }, {
    "id": "236",
    "sortname": "VA",
    "name": "Vatican City State (Holy See)",
    "phonecode": "39"
  }, {
    "id": "237",
    "sortname": "VE",
    "name": "Venezuela",
    "phonecode": "58"
  }, {
    "id": "238",
    "sortname": "VN",
    "name": "Vietnam",
    "phonecode": "84"
  }, {
    "id": "239",
    "sortname": "VG",
    "name": "Virgin Islands (British)",
    "phonecode": "1284"
  }, {
    "id": "240",
    "sortname": "VI",
    "name": "Virgin Islands (US)",
    "phonecode": "1340"
  }, {
    "id": "241",
    "sortname": "WF",
    "name": "Wallis And Futuna Islands",
    "phonecode": "681"
  }, {
    "id": "242",
    "sortname": "EH",
    "name": "Western Sahara",
    "phonecode": "212"
  }, {
    "id": "243",
    "sortname": "YE",
    "name": "Yemen",
    "phonecode": "967"
  }, {
    "id": "244",
    "sortname": "YU",
    "name": "Yugoslavia",
    "phonecode": "38"
  }, {
    "id": "245",
    "sortname": "ZM",
    "name": "Zambia",
    "phonecode": "260"
  }, {
    "id": "246",
    "sortname": "ZW",
    "name": "Zimbabwe",
    "phonecode": "263"
  }];
  var countries$1 = countries.map(function (coun) {
    return _objectSpread2({
      label: coun.name
    }, coun);
  });

  var states = [{
    "id": "1",
    "name": "Andaman and Nicobar Islands",
    "country_id": "101"
  }, {
    "id": "2",
    "name": "Andhra Pradesh",
    "country_id": "101"
  }, {
    "id": "3",
    "name": "Arunachal Pradesh",
    "country_id": "101"
  }, {
    "id": "4",
    "name": "Assam",
    "country_id": "101"
  }, {
    "id": "5",
    "name": "Bihar",
    "country_id": "101"
  }, {
    "id": "6",
    "name": "Chandigarh",
    "country_id": "101"
  }, {
    "id": "7",
    "name": "Chhattisgarh",
    "country_id": "101"
  }, {
    "id": "8",
    "name": "Dadra and Nagar Haveli",
    "country_id": "101"
  }, {
    "id": "9",
    "name": "Daman and Diu",
    "country_id": "101"
  }, {
    "id": "10",
    "name": "Delhi",
    "country_id": "101"
  }, {
    "id": "11",
    "name": "Goa",
    "country_id": "101"
  }, {
    "id": "12",
    "name": "Gujarat",
    "country_id": "101"
  }, {
    "id": "13",
    "name": "Haryana",
    "country_id": "101"
  }, {
    "id": "14",
    "name": "Himachal Pradesh",
    "country_id": "101"
  }, {
    "id": "15",
    "name": "Jammu and Kashmir",
    "country_id": "101"
  }, {
    "id": "16",
    "name": "Jharkhand",
    "country_id": "101"
  }, {
    "id": "17",
    "name": "Karnataka",
    "country_id": "101"
  }, {
    "id": "18",
    "name": "Kenmore",
    "country_id": "101"
  }, {
    "id": "19",
    "name": "Kerala",
    "country_id": "101"
  }, {
    "id": "20",
    "name": "Lakshadweep",
    "country_id": "101"
  }, {
    "id": "21",
    "name": "Madhya Pradesh",
    "country_id": "101"
  }, {
    "id": "22",
    "name": "Maharashtra",
    "country_id": "101"
  }, {
    "id": "23",
    "name": "Manipur",
    "country_id": "101"
  }, {
    "id": "24",
    "name": "Meghalaya",
    "country_id": "101"
  }, {
    "id": "25",
    "name": "Mizoram",
    "country_id": "101"
  }, {
    "id": "26",
    "name": "Nagaland",
    "country_id": "101"
  }, {
    "id": "27",
    "name": "Narora",
    "country_id": "101"
  }, {
    "id": "28",
    "name": "Natwar",
    "country_id": "101"
  }, {
    "id": "29",
    "name": "Odisha",
    "country_id": "101"
  }, {
    "id": "30",
    "name": "Paschim Medinipur",
    "country_id": "101"
  }, {
    "id": "31",
    "name": "Pondicherry",
    "country_id": "101"
  }, {
    "id": "32",
    "name": "Punjab",
    "country_id": "101"
  }, {
    "id": "33",
    "name": "Rajasthan",
    "country_id": "101"
  }, {
    "id": "34",
    "name": "Sikkim",
    "country_id": "101"
  }, {
    "id": "35",
    "name": "Tamil Nadu",
    "country_id": "101"
  }, {
    "id": "36",
    "name": "Telangana",
    "country_id": "101"
  }, {
    "id": "37",
    "name": "Tripura",
    "country_id": "101"
  }, {
    "id": "38",
    "name": "Uttar Pradesh",
    "country_id": "101"
  }, {
    "id": "39",
    "name": "Uttarakhand",
    "country_id": "101"
  }, {
    "id": "40",
    "name": "Vaishali",
    "country_id": "101"
  }, {
    "id": "41",
    "name": "West Bengal",
    "country_id": "101"
  }, {
    "id": "42",
    "name": "Badakhshan",
    "country_id": "1"
  }, {
    "id": "43",
    "name": "Badgis",
    "country_id": "1"
  }, {
    "id": "44",
    "name": "Baglan",
    "country_id": "1"
  }, {
    "id": "45",
    "name": "Balkh",
    "country_id": "1"
  }, {
    "id": "46",
    "name": "Bamiyan",
    "country_id": "1"
  }, {
    "id": "47",
    "name": "Farah",
    "country_id": "1"
  }, {
    "id": "48",
    "name": "Faryab",
    "country_id": "1"
  }, {
    "id": "49",
    "name": "Gawr",
    "country_id": "1"
  }, {
    "id": "50",
    "name": "Gazni",
    "country_id": "1"
  }, {
    "id": "51",
    "name": "Herat",
    "country_id": "1"
  }, {
    "id": "52",
    "name": "Hilmand",
    "country_id": "1"
  }, {
    "id": "53",
    "name": "Jawzjan",
    "country_id": "1"
  }, {
    "id": "54",
    "name": "Kabul",
    "country_id": "1"
  }, {
    "id": "55",
    "name": "Kapisa",
    "country_id": "1"
  }, {
    "id": "56",
    "name": "Khawst",
    "country_id": "1"
  }, {
    "id": "57",
    "name": "Kunar",
    "country_id": "1"
  }, {
    "id": "58",
    "name": "Lagman",
    "country_id": "1"
  }, {
    "id": "59",
    "name": "Lawghar",
    "country_id": "1"
  }, {
    "id": "60",
    "name": "Nangarhar",
    "country_id": "1"
  }, {
    "id": "61",
    "name": "Nimruz",
    "country_id": "1"
  }, {
    "id": "62",
    "name": "Nuristan",
    "country_id": "1"
  }, {
    "id": "63",
    "name": "Paktika",
    "country_id": "1"
  }, {
    "id": "64",
    "name": "Paktiya",
    "country_id": "1"
  }, {
    "id": "65",
    "name": "Parwan",
    "country_id": "1"
  }, {
    "id": "66",
    "name": "Qandahar",
    "country_id": "1"
  }, {
    "id": "67",
    "name": "Qunduz",
    "country_id": "1"
  }, {
    "id": "68",
    "name": "Samangan",
    "country_id": "1"
  }, {
    "id": "69",
    "name": "Sar-e Pul",
    "country_id": "1"
  }, {
    "id": "70",
    "name": "Takhar",
    "country_id": "1"
  }, {
    "id": "71",
    "name": "Uruzgan",
    "country_id": "1"
  }, {
    "id": "72",
    "name": "Wardag",
    "country_id": "1"
  }, {
    "id": "73",
    "name": "Zabul",
    "country_id": "1"
  }, {
    "id": "74",
    "name": "Berat",
    "country_id": "2"
  }, {
    "id": "75",
    "name": "Bulqize",
    "country_id": "2"
  }, {
    "id": "76",
    "name": "Delvine",
    "country_id": "2"
  }, {
    "id": "77",
    "name": "Devoll",
    "country_id": "2"
  }, {
    "id": "78",
    "name": "Dibre",
    "country_id": "2"
  }, {
    "id": "79",
    "name": "Durres",
    "country_id": "2"
  }, {
    "id": "80",
    "name": "Elbasan",
    "country_id": "2"
  }, {
    "id": "81",
    "name": "Fier",
    "country_id": "2"
  }, {
    "id": "82",
    "name": "Gjirokaster",
    "country_id": "2"
  }, {
    "id": "83",
    "name": "Gramsh",
    "country_id": "2"
  }, {
    "id": "84",
    "name": "Has",
    "country_id": "2"
  }, {
    "id": "85",
    "name": "Kavaje",
    "country_id": "2"
  }, {
    "id": "86",
    "name": "Kolonje",
    "country_id": "2"
  }, {
    "id": "87",
    "name": "Korce",
    "country_id": "2"
  }, {
    "id": "88",
    "name": "Kruje",
    "country_id": "2"
  }, {
    "id": "89",
    "name": "Kucove",
    "country_id": "2"
  }, {
    "id": "90",
    "name": "Kukes",
    "country_id": "2"
  }, {
    "id": "91",
    "name": "Kurbin",
    "country_id": "2"
  }, {
    "id": "92",
    "name": "Lezhe",
    "country_id": "2"
  }, {
    "id": "93",
    "name": "Librazhd",
    "country_id": "2"
  }, {
    "id": "94",
    "name": "Lushnje",
    "country_id": "2"
  }, {
    "id": "95",
    "name": "Mallakaster",
    "country_id": "2"
  }, {
    "id": "96",
    "name": "Malsi e Madhe",
    "country_id": "2"
  }, {
    "id": "97",
    "name": "Mat",
    "country_id": "2"
  }, {
    "id": "98",
    "name": "Mirdite",
    "country_id": "2"
  }, {
    "id": "99",
    "name": "Peqin",
    "country_id": "2"
  }, {
    "id": "100",
    "name": "Permet",
    "country_id": "2"
  }, {
    "id": "101",
    "name": "Pogradec",
    "country_id": "2"
  }, {
    "id": "102",
    "name": "Puke",
    "country_id": "2"
  }, {
    "id": "103",
    "name": "Sarande",
    "country_id": "2"
  }, {
    "id": "104",
    "name": "Shkoder",
    "country_id": "2"
  }, {
    "id": "105",
    "name": "Skrapar",
    "country_id": "2"
  }, {
    "id": "106",
    "name": "Tepelene",
    "country_id": "2"
  }, {
    "id": "107",
    "name": "Tirane",
    "country_id": "2"
  }, {
    "id": "108",
    "name": "Tropoje",
    "country_id": "2"
  }, {
    "id": "109",
    "name": "Vlore",
    "country_id": "2"
  }, {
    "id": "110",
    "name": "'Ayn Daflah",
    "country_id": "3"
  }, {
    "id": "111",
    "name": "'Ayn Tamushanat",
    "country_id": "3"
  }, {
    "id": "112",
    "name": "Adrar",
    "country_id": "3"
  }, {
    "id": "113",
    "name": "Algiers",
    "country_id": "3"
  }, {
    "id": "114",
    "name": "Annabah",
    "country_id": "3"
  }, {
    "id": "115",
    "name": "Bashshar",
    "country_id": "3"
  }, {
    "id": "116",
    "name": "Batnah",
    "country_id": "3"
  }, {
    "id": "117",
    "name": "Bijayah",
    "country_id": "3"
  }, {
    "id": "118",
    "name": "Biskrah",
    "country_id": "3"
  }, {
    "id": "119",
    "name": "Blidah",
    "country_id": "3"
  }, {
    "id": "120",
    "name": "Buirah",
    "country_id": "3"
  }, {
    "id": "121",
    "name": "Bumardas",
    "country_id": "3"
  }, {
    "id": "122",
    "name": "Burj Bu Arririj",
    "country_id": "3"
  }, {
    "id": "123",
    "name": "Ghalizan",
    "country_id": "3"
  }, {
    "id": "124",
    "name": "Ghardayah",
    "country_id": "3"
  }, {
    "id": "125",
    "name": "Ilizi",
    "country_id": "3"
  }, {
    "id": "126",
    "name": "Jijili",
    "country_id": "3"
  }, {
    "id": "127",
    "name": "Jilfah",
    "country_id": "3"
  }, {
    "id": "128",
    "name": "Khanshalah",
    "country_id": "3"
  }, {
    "id": "129",
    "name": "Masilah",
    "country_id": "3"
  }, {
    "id": "130",
    "name": "Midyah",
    "country_id": "3"
  }, {
    "id": "131",
    "name": "Milah",
    "country_id": "3"
  }, {
    "id": "132",
    "name": "Muaskar",
    "country_id": "3"
  }, {
    "id": "133",
    "name": "Mustaghanam",
    "country_id": "3"
  }, {
    "id": "134",
    "name": "Naama",
    "country_id": "3"
  }, {
    "id": "135",
    "name": "Oran",
    "country_id": "3"
  }, {
    "id": "136",
    "name": "Ouargla",
    "country_id": "3"
  }, {
    "id": "137",
    "name": "Qalmah",
    "country_id": "3"
  }, {
    "id": "138",
    "name": "Qustantinah",
    "country_id": "3"
  }, {
    "id": "139",
    "name": "Sakikdah",
    "country_id": "3"
  }, {
    "id": "140",
    "name": "Satif",
    "country_id": "3"
  }, {
    "id": "141",
    "name": "Sayda'",
    "country_id": "3"
  }, {
    "id": "142",
    "name": "Sidi ban-al-'Abbas",
    "country_id": "3"
  }, {
    "id": "143",
    "name": "Suq Ahras",
    "country_id": "3"
  }, {
    "id": "144",
    "name": "Tamanghasat",
    "country_id": "3"
  }, {
    "id": "145",
    "name": "Tibazah",
    "country_id": "3"
  }, {
    "id": "146",
    "name": "Tibissah",
    "country_id": "3"
  }, {
    "id": "147",
    "name": "Tilimsan",
    "country_id": "3"
  }, {
    "id": "148",
    "name": "Tinduf",
    "country_id": "3"
  }, {
    "id": "149",
    "name": "Tisamsilt",
    "country_id": "3"
  }, {
    "id": "150",
    "name": "Tiyarat",
    "country_id": "3"
  }, {
    "id": "151",
    "name": "Tizi Wazu",
    "country_id": "3"
  }, {
    "id": "152",
    "name": "Umm-al-Bawaghi",
    "country_id": "3"
  }, {
    "id": "153",
    "name": "Wahran",
    "country_id": "3"
  }, {
    "id": "154",
    "name": "Warqla",
    "country_id": "3"
  }, {
    "id": "155",
    "name": "Wilaya d Alger",
    "country_id": "3"
  }, {
    "id": "156",
    "name": "Wilaya de Bejaia",
    "country_id": "3"
  }, {
    "id": "157",
    "name": "Wilaya de Constantine",
    "country_id": "3"
  }, {
    "id": "158",
    "name": "al-Aghwat",
    "country_id": "3"
  }, {
    "id": "159",
    "name": "al-Bayadh",
    "country_id": "3"
  }, {
    "id": "160",
    "name": "al-Jaza'ir",
    "country_id": "3"
  }, {
    "id": "161",
    "name": "al-Wad",
    "country_id": "3"
  }, {
    "id": "162",
    "name": "ash-Shalif",
    "country_id": "3"
  }, {
    "id": "163",
    "name": "at-Tarif",
    "country_id": "3"
  }, {
    "id": "164",
    "name": "Eastern",
    "country_id": "4"
  }, {
    "id": "165",
    "name": "Manu'a",
    "country_id": "4"
  }, {
    "id": "166",
    "name": "Swains Island",
    "country_id": "4"
  }, {
    "id": "167",
    "name": "Western",
    "country_id": "4"
  }, {
    "id": "168",
    "name": "Andorra la Vella",
    "country_id": "5"
  }, {
    "id": "169",
    "name": "Canillo",
    "country_id": "5"
  }, {
    "id": "170",
    "name": "Encamp",
    "country_id": "5"
  }, {
    "id": "171",
    "name": "La Massana",
    "country_id": "5"
  }, {
    "id": "172",
    "name": "Les Escaldes",
    "country_id": "5"
  }, {
    "id": "173",
    "name": "Ordino",
    "country_id": "5"
  }, {
    "id": "174",
    "name": "Sant Julia de Loria",
    "country_id": "5"
  }, {
    "id": "175",
    "name": "Bengo",
    "country_id": "6"
  }, {
    "id": "176",
    "name": "Benguela",
    "country_id": "6"
  }, {
    "id": "177",
    "name": "Bie",
    "country_id": "6"
  }, {
    "id": "178",
    "name": "Cabinda",
    "country_id": "6"
  }, {
    "id": "179",
    "name": "Cunene",
    "country_id": "6"
  }, {
    "id": "180",
    "name": "Huambo",
    "country_id": "6"
  }, {
    "id": "181",
    "name": "Huila",
    "country_id": "6"
  }, {
    "id": "182",
    "name": "Kuando-Kubango",
    "country_id": "6"
  }, {
    "id": "183",
    "name": "Kwanza Norte",
    "country_id": "6"
  }, {
    "id": "184",
    "name": "Kwanza Sul",
    "country_id": "6"
  }, {
    "id": "185",
    "name": "Luanda",
    "country_id": "6"
  }, {
    "id": "186",
    "name": "Lunda Norte",
    "country_id": "6"
  }, {
    "id": "187",
    "name": "Lunda Sul",
    "country_id": "6"
  }, {
    "id": "188",
    "name": "Malanje",
    "country_id": "6"
  }, {
    "id": "189",
    "name": "Moxico",
    "country_id": "6"
  }, {
    "id": "190",
    "name": "Namibe",
    "country_id": "6"
  }, {
    "id": "191",
    "name": "Uige",
    "country_id": "6"
  }, {
    "id": "192",
    "name": "Zaire",
    "country_id": "6"
  }, {
    "id": "193",
    "name": "Other Provinces",
    "country_id": "7"
  }, {
    "id": "194",
    "name": "Sector claimed by Argentina\/Ch",
    "country_id": "8"
  }, {
    "id": "195",
    "name": "Sector claimed by Argentina\/UK",
    "country_id": "8"
  }, {
    "id": "196",
    "name": "Sector claimed by Australia",
    "country_id": "8"
  }, {
    "id": "197",
    "name": "Sector claimed by France",
    "country_id": "8"
  }, {
    "id": "198",
    "name": "Sector claimed by New Zealand",
    "country_id": "8"
  }, {
    "id": "199",
    "name": "Sector claimed by Norway",
    "country_id": "8"
  }, {
    "id": "200",
    "name": "Unclaimed Sector",
    "country_id": "8"
  }, {
    "id": "201",
    "name": "Barbuda",
    "country_id": "9"
  }, {
    "id": "202",
    "name": "Saint George",
    "country_id": "9"
  }, {
    "id": "203",
    "name": "Saint John",
    "country_id": "9"
  }, {
    "id": "204",
    "name": "Saint Mary",
    "country_id": "9"
  }, {
    "id": "205",
    "name": "Saint Paul",
    "country_id": "9"
  }, {
    "id": "206",
    "name": "Saint Peter",
    "country_id": "9"
  }, {
    "id": "207",
    "name": "Saint Philip",
    "country_id": "9"
  }, {
    "id": "208",
    "name": "Buenos Aires",
    "country_id": "10"
  }, {
    "id": "209",
    "name": "Catamarca",
    "country_id": "10"
  }, {
    "id": "210",
    "name": "Chaco",
    "country_id": "10"
  }, {
    "id": "211",
    "name": "Chubut",
    "country_id": "10"
  }, {
    "id": "212",
    "name": "Cordoba",
    "country_id": "10"
  }, {
    "id": "213",
    "name": "Corrientes",
    "country_id": "10"
  }, {
    "id": "214",
    "name": "Distrito Federal",
    "country_id": "10"
  }, {
    "id": "215",
    "name": "Entre Rios",
    "country_id": "10"
  }, {
    "id": "216",
    "name": "Formosa",
    "country_id": "10"
  }, {
    "id": "217",
    "name": "Jujuy",
    "country_id": "10"
  }, {
    "id": "218",
    "name": "La Pampa",
    "country_id": "10"
  }, {
    "id": "219",
    "name": "La Rioja",
    "country_id": "10"
  }, {
    "id": "220",
    "name": "Mendoza",
    "country_id": "10"
  }, {
    "id": "221",
    "name": "Misiones",
    "country_id": "10"
  }, {
    "id": "222",
    "name": "Neuquen",
    "country_id": "10"
  }, {
    "id": "223",
    "name": "Rio Negro",
    "country_id": "10"
  }, {
    "id": "224",
    "name": "Salta",
    "country_id": "10"
  }, {
    "id": "225",
    "name": "San Juan",
    "country_id": "10"
  }, {
    "id": "226",
    "name": "San Luis",
    "country_id": "10"
  }, {
    "id": "227",
    "name": "Santa Cruz",
    "country_id": "10"
  }, {
    "id": "228",
    "name": "Santa Fe",
    "country_id": "10"
  }, {
    "id": "229",
    "name": "Santiago del Estero",
    "country_id": "10"
  }, {
    "id": "230",
    "name": "Tierra del Fuego",
    "country_id": "10"
  }, {
    "id": "231",
    "name": "Tucuman",
    "country_id": "10"
  }, {
    "id": "232",
    "name": "Aragatsotn",
    "country_id": "11"
  }, {
    "id": "233",
    "name": "Ararat",
    "country_id": "11"
  }, {
    "id": "234",
    "name": "Armavir",
    "country_id": "11"
  }, {
    "id": "235",
    "name": "Gegharkunik",
    "country_id": "11"
  }, {
    "id": "236",
    "name": "Kotaik",
    "country_id": "11"
  }, {
    "id": "237",
    "name": "Lori",
    "country_id": "11"
  }, {
    "id": "238",
    "name": "Shirak",
    "country_id": "11"
  }, {
    "id": "239",
    "name": "Stepanakert",
    "country_id": "11"
  }, {
    "id": "240",
    "name": "Syunik",
    "country_id": "11"
  }, {
    "id": "241",
    "name": "Tavush",
    "country_id": "11"
  }, {
    "id": "242",
    "name": "Vayots Dzor",
    "country_id": "11"
  }, {
    "id": "243",
    "name": "Yerevan",
    "country_id": "11"
  }, {
    "id": "244",
    "name": "Aruba",
    "country_id": "12"
  }, {
    "id": "245",
    "name": "Auckland",
    "country_id": "13"
  }, {
    "id": "246",
    "name": "Australian Capital Territory",
    "country_id": "13"
  }, {
    "id": "247",
    "name": "Balgowlah",
    "country_id": "13"
  }, {
    "id": "248",
    "name": "Balmain",
    "country_id": "13"
  }, {
    "id": "249",
    "name": "Bankstown",
    "country_id": "13"
  }, {
    "id": "250",
    "name": "Baulkham Hills",
    "country_id": "13"
  }, {
    "id": "251",
    "name": "Bonnet Bay",
    "country_id": "13"
  }, {
    "id": "252",
    "name": "Camberwell",
    "country_id": "13"
  }, {
    "id": "253",
    "name": "Carole Park",
    "country_id": "13"
  }, {
    "id": "254",
    "name": "Castle Hill",
    "country_id": "13"
  }, {
    "id": "255",
    "name": "Caulfield",
    "country_id": "13"
  }, {
    "id": "256",
    "name": "Chatswood",
    "country_id": "13"
  }, {
    "id": "257",
    "name": "Cheltenham",
    "country_id": "13"
  }, {
    "id": "258",
    "name": "Cherrybrook",
    "country_id": "13"
  }, {
    "id": "259",
    "name": "Clayton",
    "country_id": "13"
  }, {
    "id": "260",
    "name": "Collingwood",
    "country_id": "13"
  }, {
    "id": "261",
    "name": "Frenchs Forest",
    "country_id": "13"
  }, {
    "id": "262",
    "name": "Hawthorn",
    "country_id": "13"
  }, {
    "id": "263",
    "name": "Jannnali",
    "country_id": "13"
  }, {
    "id": "264",
    "name": "Knoxfield",
    "country_id": "13"
  }, {
    "id": "265",
    "name": "Melbourne",
    "country_id": "13"
  }, {
    "id": "266",
    "name": "New South Wales",
    "country_id": "13"
  }, {
    "id": "267",
    "name": "Northern Territory",
    "country_id": "13"
  }, {
    "id": "268",
    "name": "Perth",
    "country_id": "13"
  }, {
    "id": "269",
    "name": "Queensland",
    "country_id": "13"
  }, {
    "id": "270",
    "name": "South Australia",
    "country_id": "13"
  }, {
    "id": "271",
    "name": "Tasmania",
    "country_id": "13"
  }, {
    "id": "272",
    "name": "Templestowe",
    "country_id": "13"
  }, {
    "id": "273",
    "name": "Victoria",
    "country_id": "13"
  }, {
    "id": "274",
    "name": "Werribee south",
    "country_id": "13"
  }, {
    "id": "275",
    "name": "Western Australia",
    "country_id": "13"
  }, {
    "id": "276",
    "name": "Wheeler",
    "country_id": "13"
  }, {
    "id": "277",
    "name": "Bundesland Salzburg",
    "country_id": "14"
  }, {
    "id": "278",
    "name": "Bundesland Steiermark",
    "country_id": "14"
  }, {
    "id": "279",
    "name": "Bundesland Tirol",
    "country_id": "14"
  }, {
    "id": "280",
    "name": "Burgenland",
    "country_id": "14"
  }, {
    "id": "281",
    "name": "Carinthia",
    "country_id": "14"
  }, {
    "id": "282",
    "name": "Karnten",
    "country_id": "14"
  }, {
    "id": "283",
    "name": "Liezen",
    "country_id": "14"
  }, {
    "id": "284",
    "name": "Lower Austria",
    "country_id": "14"
  }, {
    "id": "285",
    "name": "Niederosterreich",
    "country_id": "14"
  }, {
    "id": "286",
    "name": "Oberosterreich",
    "country_id": "14"
  }, {
    "id": "287",
    "name": "Salzburg",
    "country_id": "14"
  }, {
    "id": "288",
    "name": "Schleswig-Holstein",
    "country_id": "14"
  }, {
    "id": "289",
    "name": "Steiermark",
    "country_id": "14"
  }, {
    "id": "290",
    "name": "Styria",
    "country_id": "14"
  }, {
    "id": "291",
    "name": "Tirol",
    "country_id": "14"
  }, {
    "id": "292",
    "name": "Upper Austria",
    "country_id": "14"
  }, {
    "id": "293",
    "name": "Vorarlberg",
    "country_id": "14"
  }, {
    "id": "294",
    "name": "Wien",
    "country_id": "14"
  }, {
    "id": "295",
    "name": "Abseron",
    "country_id": "15"
  }, {
    "id": "296",
    "name": "Baki Sahari",
    "country_id": "15"
  }, {
    "id": "297",
    "name": "Ganca",
    "country_id": "15"
  }, {
    "id": "298",
    "name": "Ganja",
    "country_id": "15"
  }, {
    "id": "299",
    "name": "Kalbacar",
    "country_id": "15"
  }, {
    "id": "300",
    "name": "Lankaran",
    "country_id": "15"
  }, {
    "id": "301",
    "name": "Mil-Qarabax",
    "country_id": "15"
  }, {
    "id": "302",
    "name": "Mugan-Salyan",
    "country_id": "15"
  }, {
    "id": "303",
    "name": "Nagorni-Qarabax",
    "country_id": "15"
  }, {
    "id": "304",
    "name": "Naxcivan",
    "country_id": "15"
  }, {
    "id": "305",
    "name": "Priaraks",
    "country_id": "15"
  }, {
    "id": "306",
    "name": "Qazax",
    "country_id": "15"
  }, {
    "id": "307",
    "name": "Saki",
    "country_id": "15"
  }, {
    "id": "308",
    "name": "Sirvan",
    "country_id": "15"
  }, {
    "id": "309",
    "name": "Xacmaz",
    "country_id": "15"
  }, {
    "id": "310",
    "name": "Abaco",
    "country_id": "16"
  }, {
    "id": "311",
    "name": "Acklins Island",
    "country_id": "16"
  }, {
    "id": "312",
    "name": "Andros",
    "country_id": "16"
  }, {
    "id": "313",
    "name": "Berry Islands",
    "country_id": "16"
  }, {
    "id": "314",
    "name": "Biminis",
    "country_id": "16"
  }, {
    "id": "315",
    "name": "Cat Island",
    "country_id": "16"
  }, {
    "id": "316",
    "name": "Crooked Island",
    "country_id": "16"
  }, {
    "id": "317",
    "name": "Eleuthera",
    "country_id": "16"
  }, {
    "id": "318",
    "name": "Exuma and Cays",
    "country_id": "16"
  }, {
    "id": "319",
    "name": "Grand Bahama",
    "country_id": "16"
  }, {
    "id": "320",
    "name": "Inagua Islands",
    "country_id": "16"
  }, {
    "id": "321",
    "name": "Long Island",
    "country_id": "16"
  }, {
    "id": "322",
    "name": "Mayaguana",
    "country_id": "16"
  }, {
    "id": "323",
    "name": "New Providence",
    "country_id": "16"
  }, {
    "id": "324",
    "name": "Ragged Island",
    "country_id": "16"
  }, {
    "id": "325",
    "name": "Rum Cay",
    "country_id": "16"
  }, {
    "id": "326",
    "name": "San Salvador",
    "country_id": "16"
  }, {
    "id": "327",
    "name": "'Isa",
    "country_id": "17"
  }, {
    "id": "328",
    "name": "Badiyah",
    "country_id": "17"
  }, {
    "id": "329",
    "name": "Hidd",
    "country_id": "17"
  }, {
    "id": "330",
    "name": "Jidd Hafs",
    "country_id": "17"
  }, {
    "id": "331",
    "name": "Mahama",
    "country_id": "17"
  }, {
    "id": "332",
    "name": "Manama",
    "country_id": "17"
  }, {
    "id": "333",
    "name": "Sitrah",
    "country_id": "17"
  }, {
    "id": "334",
    "name": "al-Manamah",
    "country_id": "17"
  }, {
    "id": "335",
    "name": "al-Muharraq",
    "country_id": "17"
  }, {
    "id": "336",
    "name": "ar-Rifa'a",
    "country_id": "17"
  }, {
    "id": "337",
    "name": "Bagar Hat",
    "country_id": "18"
  }, {
    "id": "338",
    "name": "Bandarban",
    "country_id": "18"
  }, {
    "id": "339",
    "name": "Barguna",
    "country_id": "18"
  }, {
    "id": "340",
    "name": "Barisal",
    "country_id": "18"
  }, {
    "id": "341",
    "name": "Bhola",
    "country_id": "18"
  }, {
    "id": "342",
    "name": "Bogora",
    "country_id": "18"
  }, {
    "id": "343",
    "name": "Brahman Bariya",
    "country_id": "18"
  }, {
    "id": "344",
    "name": "Chandpur",
    "country_id": "18"
  }, {
    "id": "345",
    "name": "Chattagam",
    "country_id": "18"
  }, {
    "id": "346",
    "name": "Chittagong Division",
    "country_id": "18"
  }, {
    "id": "347",
    "name": "Chuadanga",
    "country_id": "18"
  }, {
    "id": "348",
    "name": "Dhaka",
    "country_id": "18"
  }, {
    "id": "349",
    "name": "Dinajpur",
    "country_id": "18"
  }, {
    "id": "350",
    "name": "Faridpur",
    "country_id": "18"
  }, {
    "id": "351",
    "name": "Feni",
    "country_id": "18"
  }, {
    "id": "352",
    "name": "Gaybanda",
    "country_id": "18"
  }, {
    "id": "353",
    "name": "Gazipur",
    "country_id": "18"
  }, {
    "id": "354",
    "name": "Gopalganj",
    "country_id": "18"
  }, {
    "id": "355",
    "name": "Habiganj",
    "country_id": "18"
  }, {
    "id": "356",
    "name": "Jaipur Hat",
    "country_id": "18"
  }, {
    "id": "357",
    "name": "Jamalpur",
    "country_id": "18"
  }, {
    "id": "358",
    "name": "Jessor",
    "country_id": "18"
  }, {
    "id": "359",
    "name": "Jhalakati",
    "country_id": "18"
  }, {
    "id": "360",
    "name": "Jhanaydah",
    "country_id": "18"
  }, {
    "id": "361",
    "name": "Khagrachhari",
    "country_id": "18"
  }, {
    "id": "362",
    "name": "Khulna",
    "country_id": "18"
  }, {
    "id": "363",
    "name": "Kishorganj",
    "country_id": "18"
  }, {
    "id": "364",
    "name": "Koks Bazar",
    "country_id": "18"
  }, {
    "id": "365",
    "name": "Komilla",
    "country_id": "18"
  }, {
    "id": "366",
    "name": "Kurigram",
    "country_id": "18"
  }, {
    "id": "367",
    "name": "Kushtiya",
    "country_id": "18"
  }, {
    "id": "368",
    "name": "Lakshmipur",
    "country_id": "18"
  }, {
    "id": "369",
    "name": "Lalmanir Hat",
    "country_id": "18"
  }, {
    "id": "370",
    "name": "Madaripur",
    "country_id": "18"
  }, {
    "id": "371",
    "name": "Magura",
    "country_id": "18"
  }, {
    "id": "372",
    "name": "Maimansingh",
    "country_id": "18"
  }, {
    "id": "373",
    "name": "Manikganj",
    "country_id": "18"
  }, {
    "id": "374",
    "name": "Maulvi Bazar",
    "country_id": "18"
  }, {
    "id": "375",
    "name": "Meherpur",
    "country_id": "18"
  }, {
    "id": "376",
    "name": "Munshiganj",
    "country_id": "18"
  }, {
    "id": "377",
    "name": "Naral",
    "country_id": "18"
  }, {
    "id": "378",
    "name": "Narayanganj",
    "country_id": "18"
  }, {
    "id": "379",
    "name": "Narsingdi",
    "country_id": "18"
  }, {
    "id": "380",
    "name": "Nator",
    "country_id": "18"
  }, {
    "id": "381",
    "name": "Naugaon",
    "country_id": "18"
  }, {
    "id": "382",
    "name": "Nawabganj",
    "country_id": "18"
  }, {
    "id": "383",
    "name": "Netrakona",
    "country_id": "18"
  }, {
    "id": "384",
    "name": "Nilphamari",
    "country_id": "18"
  }, {
    "id": "385",
    "name": "Noakhali",
    "country_id": "18"
  }, {
    "id": "386",
    "name": "Pabna",
    "country_id": "18"
  }, {
    "id": "387",
    "name": "Panchagarh",
    "country_id": "18"
  }, {
    "id": "388",
    "name": "Patuakhali",
    "country_id": "18"
  }, {
    "id": "389",
    "name": "Pirojpur",
    "country_id": "18"
  }, {
    "id": "390",
    "name": "Rajbari",
    "country_id": "18"
  }, {
    "id": "391",
    "name": "Rajshahi",
    "country_id": "18"
  }, {
    "id": "392",
    "name": "Rangamati",
    "country_id": "18"
  }, {
    "id": "393",
    "name": "Rangpur",
    "country_id": "18"
  }, {
    "id": "394",
    "name": "Satkhira",
    "country_id": "18"
  }, {
    "id": "395",
    "name": "Shariatpur",
    "country_id": "18"
  }, {
    "id": "396",
    "name": "Sherpur",
    "country_id": "18"
  }, {
    "id": "397",
    "name": "Silhat",
    "country_id": "18"
  }, {
    "id": "398",
    "name": "Sirajganj",
    "country_id": "18"
  }, {
    "id": "399",
    "name": "Sunamganj",
    "country_id": "18"
  }, {
    "id": "400",
    "name": "Tangayal",
    "country_id": "18"
  }, {
    "id": "401",
    "name": "Thakurgaon",
    "country_id": "18"
  }, {
    "id": "402",
    "name": "Christ Church",
    "country_id": "19"
  }, {
    "id": "403",
    "name": "Saint Andrew",
    "country_id": "19"
  }, {
    "id": "404",
    "name": "Saint George",
    "country_id": "19"
  }, {
    "id": "405",
    "name": "Saint James",
    "country_id": "19"
  }, {
    "id": "406",
    "name": "Saint John",
    "country_id": "19"
  }, {
    "id": "407",
    "name": "Saint Joseph",
    "country_id": "19"
  }, {
    "id": "408",
    "name": "Saint Lucy",
    "country_id": "19"
  }, {
    "id": "409",
    "name": "Saint Michael",
    "country_id": "19"
  }, {
    "id": "410",
    "name": "Saint Peter",
    "country_id": "19"
  }, {
    "id": "411",
    "name": "Saint Philip",
    "country_id": "19"
  }, {
    "id": "412",
    "name": "Saint Thomas",
    "country_id": "19"
  }, {
    "id": "413",
    "name": "Brest",
    "country_id": "20"
  }, {
    "id": "414",
    "name": "Homjel'",
    "country_id": "20"
  }, {
    "id": "415",
    "name": "Hrodna",
    "country_id": "20"
  }, {
    "id": "416",
    "name": "Mahiljow",
    "country_id": "20"
  }, {
    "id": "417",
    "name": "Mahilyowskaya Voblasts",
    "country_id": "20"
  }, {
    "id": "418",
    "name": "Minsk",
    "country_id": "20"
  }, {
    "id": "419",
    "name": "Minskaja Voblasts'",
    "country_id": "20"
  }, {
    "id": "420",
    "name": "Petrik",
    "country_id": "20"
  }, {
    "id": "421",
    "name": "Vicebsk",
    "country_id": "20"
  }, {
    "id": "422",
    "name": "Antwerpen",
    "country_id": "21"
  }, {
    "id": "423",
    "name": "Berchem",
    "country_id": "21"
  }, {
    "id": "424",
    "name": "Brabant",
    "country_id": "21"
  }, {
    "id": "425",
    "name": "Brabant Wallon",
    "country_id": "21"
  }, {
    "id": "426",
    "name": "Brussel",
    "country_id": "21"
  }, {
    "id": "427",
    "name": "East Flanders",
    "country_id": "21"
  }, {
    "id": "428",
    "name": "Hainaut",
    "country_id": "21"
  }, {
    "id": "429",
    "name": "Liege",
    "country_id": "21"
  }, {
    "id": "430",
    "name": "Limburg",
    "country_id": "21"
  }, {
    "id": "431",
    "name": "Luxembourg",
    "country_id": "21"
  }, {
    "id": "432",
    "name": "Namur",
    "country_id": "21"
  }, {
    "id": "433",
    "name": "Ontario",
    "country_id": "21"
  }, {
    "id": "434",
    "name": "Oost-Vlaanderen",
    "country_id": "21"
  }, {
    "id": "435",
    "name": "Provincie Brabant",
    "country_id": "21"
  }, {
    "id": "436",
    "name": "Vlaams-Brabant",
    "country_id": "21"
  }, {
    "id": "437",
    "name": "Wallonne",
    "country_id": "21"
  }, {
    "id": "438",
    "name": "West-Vlaanderen",
    "country_id": "21"
  }, {
    "id": "439",
    "name": "Belize",
    "country_id": "22"
  }, {
    "id": "440",
    "name": "Cayo",
    "country_id": "22"
  }, {
    "id": "441",
    "name": "Corozal",
    "country_id": "22"
  }, {
    "id": "442",
    "name": "Orange Walk",
    "country_id": "22"
  }, {
    "id": "443",
    "name": "Stann Creek",
    "country_id": "22"
  }, {
    "id": "444",
    "name": "Toledo",
    "country_id": "22"
  }, {
    "id": "445",
    "name": "Alibori",
    "country_id": "23"
  }, {
    "id": "446",
    "name": "Atacora",
    "country_id": "23"
  }, {
    "id": "447",
    "name": "Atlantique",
    "country_id": "23"
  }, {
    "id": "448",
    "name": "Borgou",
    "country_id": "23"
  }, {
    "id": "449",
    "name": "Collines",
    "country_id": "23"
  }, {
    "id": "450",
    "name": "Couffo",
    "country_id": "23"
  }, {
    "id": "451",
    "name": "Donga",
    "country_id": "23"
  }, {
    "id": "452",
    "name": "Littoral",
    "country_id": "23"
  }, {
    "id": "453",
    "name": "Mono",
    "country_id": "23"
  }, {
    "id": "454",
    "name": "Oueme",
    "country_id": "23"
  }, {
    "id": "455",
    "name": "Plateau",
    "country_id": "23"
  }, {
    "id": "456",
    "name": "Zou",
    "country_id": "23"
  }, {
    "id": "457",
    "name": "Hamilton",
    "country_id": "24"
  }, {
    "id": "458",
    "name": "Saint George",
    "country_id": "24"
  }, {
    "id": "459",
    "name": "Bumthang",
    "country_id": "25"
  }, {
    "id": "460",
    "name": "Chhukha",
    "country_id": "25"
  }, {
    "id": "461",
    "name": "Chirang",
    "country_id": "25"
  }, {
    "id": "462",
    "name": "Daga",
    "country_id": "25"
  }, {
    "id": "463",
    "name": "Geylegphug",
    "country_id": "25"
  }, {
    "id": "464",
    "name": "Ha",
    "country_id": "25"
  }, {
    "id": "465",
    "name": "Lhuntshi",
    "country_id": "25"
  }, {
    "id": "466",
    "name": "Mongar",
    "country_id": "25"
  }, {
    "id": "467",
    "name": "Pemagatsel",
    "country_id": "25"
  }, {
    "id": "468",
    "name": "Punakha",
    "country_id": "25"
  }, {
    "id": "469",
    "name": "Rinpung",
    "country_id": "25"
  }, {
    "id": "470",
    "name": "Samchi",
    "country_id": "25"
  }, {
    "id": "471",
    "name": "Samdrup Jongkhar",
    "country_id": "25"
  }, {
    "id": "472",
    "name": "Shemgang",
    "country_id": "25"
  }, {
    "id": "473",
    "name": "Tashigang",
    "country_id": "25"
  }, {
    "id": "474",
    "name": "Timphu",
    "country_id": "25"
  }, {
    "id": "475",
    "name": "Tongsa",
    "country_id": "25"
  }, {
    "id": "476",
    "name": "Wangdiphodrang",
    "country_id": "25"
  }, {
    "id": "477",
    "name": "Beni",
    "country_id": "26"
  }, {
    "id": "478",
    "name": "Chuquisaca",
    "country_id": "26"
  }, {
    "id": "479",
    "name": "Cochabamba",
    "country_id": "26"
  }, {
    "id": "480",
    "name": "La Paz",
    "country_id": "26"
  }, {
    "id": "481",
    "name": "Oruro",
    "country_id": "26"
  }, {
    "id": "482",
    "name": "Pando",
    "country_id": "26"
  }, {
    "id": "483",
    "name": "Potosi",
    "country_id": "26"
  }, {
    "id": "484",
    "name": "Santa Cruz",
    "country_id": "26"
  }, {
    "id": "485",
    "name": "Tarija",
    "country_id": "26"
  }, {
    "id": "486",
    "name": "Federacija Bosna i Hercegovina",
    "country_id": "27"
  }, {
    "id": "487",
    "name": "Republika Srpska",
    "country_id": "27"
  }, {
    "id": "488",
    "name": "Central Bobonong",
    "country_id": "28"
  }, {
    "id": "489",
    "name": "Central Boteti",
    "country_id": "28"
  }, {
    "id": "490",
    "name": "Central Mahalapye",
    "country_id": "28"
  }, {
    "id": "491",
    "name": "Central Serowe-Palapye",
    "country_id": "28"
  }, {
    "id": "492",
    "name": "Central Tutume",
    "country_id": "28"
  }, {
    "id": "493",
    "name": "Chobe",
    "country_id": "28"
  }, {
    "id": "494",
    "name": "Francistown",
    "country_id": "28"
  }, {
    "id": "495",
    "name": "Gaborone",
    "country_id": "28"
  }, {
    "id": "496",
    "name": "Ghanzi",
    "country_id": "28"
  }, {
    "id": "497",
    "name": "Jwaneng",
    "country_id": "28"
  }, {
    "id": "498",
    "name": "Kgalagadi North",
    "country_id": "28"
  }, {
    "id": "499",
    "name": "Kgalagadi South",
    "country_id": "28"
  }, {
    "id": "500",
    "name": "Kgatleng",
    "country_id": "28"
  }, {
    "id": "501",
    "name": "Kweneng",
    "country_id": "28"
  }, {
    "id": "502",
    "name": "Lobatse",
    "country_id": "28"
  }, {
    "id": "503",
    "name": "Ngamiland",
    "country_id": "28"
  }, {
    "id": "504",
    "name": "Ngwaketse",
    "country_id": "28"
  }, {
    "id": "505",
    "name": "North East",
    "country_id": "28"
  }, {
    "id": "506",
    "name": "Okavango",
    "country_id": "28"
  }, {
    "id": "507",
    "name": "Orapa",
    "country_id": "28"
  }, {
    "id": "508",
    "name": "Selibe Phikwe",
    "country_id": "28"
  }, {
    "id": "509",
    "name": "South East",
    "country_id": "28"
  }, {
    "id": "510",
    "name": "Sowa",
    "country_id": "28"
  }, {
    "id": "511",
    "name": "Bouvet Island",
    "country_id": "29"
  }, {
    "id": "512",
    "name": "Acre",
    "country_id": "30"
  }, {
    "id": "513",
    "name": "Alagoas",
    "country_id": "30"
  }, {
    "id": "514",
    "name": "Amapa",
    "country_id": "30"
  }, {
    "id": "515",
    "name": "Amazonas",
    "country_id": "30"
  }, {
    "id": "516",
    "name": "Bahia",
    "country_id": "30"
  }, {
    "id": "517",
    "name": "Ceara",
    "country_id": "30"
  }, {
    "id": "518",
    "name": "Distrito Federal",
    "country_id": "30"
  }, {
    "id": "519",
    "name": "Espirito Santo",
    "country_id": "30"
  }, {
    "id": "520",
    "name": "Estado de Sao Paulo",
    "country_id": "30"
  }, {
    "id": "521",
    "name": "Goias",
    "country_id": "30"
  }, {
    "id": "522",
    "name": "Maranhao",
    "country_id": "30"
  }, {
    "id": "523",
    "name": "Mato Grosso",
    "country_id": "30"
  }, {
    "id": "524",
    "name": "Mato Grosso do Sul",
    "country_id": "30"
  }, {
    "id": "525",
    "name": "Minas Gerais",
    "country_id": "30"
  }, {
    "id": "526",
    "name": "Para",
    "country_id": "30"
  }, {
    "id": "527",
    "name": "Paraiba",
    "country_id": "30"
  }, {
    "id": "528",
    "name": "Parana",
    "country_id": "30"
  }, {
    "id": "529",
    "name": "Pernambuco",
    "country_id": "30"
  }, {
    "id": "530",
    "name": "Piaui",
    "country_id": "30"
  }, {
    "id": "531",
    "name": "Rio Grande do Norte",
    "country_id": "30"
  }, {
    "id": "532",
    "name": "Rio Grande do Sul",
    "country_id": "30"
  }, {
    "id": "533",
    "name": "Rio de Janeiro",
    "country_id": "30"
  }, {
    "id": "534",
    "name": "Rondonia",
    "country_id": "30"
  }, {
    "id": "535",
    "name": "Roraima",
    "country_id": "30"
  }, {
    "id": "536",
    "name": "Santa Catarina",
    "country_id": "30"
  }, {
    "id": "537",
    "name": "Sao Paulo",
    "country_id": "30"
  }, {
    "id": "538",
    "name": "Sergipe",
    "country_id": "30"
  }, {
    "id": "539",
    "name": "Tocantins",
    "country_id": "30"
  }, {
    "id": "540",
    "name": "British Indian Ocean Territory",
    "country_id": "31"
  }, {
    "id": "541",
    "name": "Belait",
    "country_id": "32"
  }, {
    "id": "542",
    "name": "Brunei-Muara",
    "country_id": "32"
  }, {
    "id": "543",
    "name": "Temburong",
    "country_id": "32"
  }, {
    "id": "544",
    "name": "Tutong",
    "country_id": "32"
  }, {
    "id": "545",
    "name": "Blagoevgrad",
    "country_id": "33"
  }, {
    "id": "546",
    "name": "Burgas",
    "country_id": "33"
  }, {
    "id": "547",
    "name": "Dobrich",
    "country_id": "33"
  }, {
    "id": "548",
    "name": "Gabrovo",
    "country_id": "33"
  }, {
    "id": "549",
    "name": "Haskovo",
    "country_id": "33"
  }, {
    "id": "550",
    "name": "Jambol",
    "country_id": "33"
  }, {
    "id": "551",
    "name": "Kardzhali",
    "country_id": "33"
  }, {
    "id": "552",
    "name": "Kjustendil",
    "country_id": "33"
  }, {
    "id": "553",
    "name": "Lovech",
    "country_id": "33"
  }, {
    "id": "554",
    "name": "Montana",
    "country_id": "33"
  }, {
    "id": "555",
    "name": "Oblast Sofiya-Grad",
    "country_id": "33"
  }, {
    "id": "556",
    "name": "Pazardzhik",
    "country_id": "33"
  }, {
    "id": "557",
    "name": "Pernik",
    "country_id": "33"
  }, {
    "id": "558",
    "name": "Pleven",
    "country_id": "33"
  }, {
    "id": "559",
    "name": "Plovdiv",
    "country_id": "33"
  }, {
    "id": "560",
    "name": "Razgrad",
    "country_id": "33"
  }, {
    "id": "561",
    "name": "Ruse",
    "country_id": "33"
  }, {
    "id": "562",
    "name": "Shumen",
    "country_id": "33"
  }, {
    "id": "563",
    "name": "Silistra",
    "country_id": "33"
  }, {
    "id": "564",
    "name": "Sliven",
    "country_id": "33"
  }, {
    "id": "565",
    "name": "Smoljan",
    "country_id": "33"
  }, {
    "id": "566",
    "name": "Sofija grad",
    "country_id": "33"
  }, {
    "id": "567",
    "name": "Sofijska oblast",
    "country_id": "33"
  }, {
    "id": "568",
    "name": "Stara Zagora",
    "country_id": "33"
  }, {
    "id": "569",
    "name": "Targovishte",
    "country_id": "33"
  }, {
    "id": "570",
    "name": "Varna",
    "country_id": "33"
  }, {
    "id": "571",
    "name": "Veliko Tarnovo",
    "country_id": "33"
  }, {
    "id": "572",
    "name": "Vidin",
    "country_id": "33"
  }, {
    "id": "573",
    "name": "Vraca",
    "country_id": "33"
  }, {
    "id": "574",
    "name": "Yablaniza",
    "country_id": "33"
  }, {
    "id": "575",
    "name": "Bale",
    "country_id": "34"
  }, {
    "id": "576",
    "name": "Bam",
    "country_id": "34"
  }, {
    "id": "577",
    "name": "Bazega",
    "country_id": "34"
  }, {
    "id": "578",
    "name": "Bougouriba",
    "country_id": "34"
  }, {
    "id": "579",
    "name": "Boulgou",
    "country_id": "34"
  }, {
    "id": "580",
    "name": "Boulkiemde",
    "country_id": "34"
  }, {
    "id": "581",
    "name": "Comoe",
    "country_id": "34"
  }, {
    "id": "582",
    "name": "Ganzourgou",
    "country_id": "34"
  }, {
    "id": "583",
    "name": "Gnagna",
    "country_id": "34"
  }, {
    "id": "584",
    "name": "Gourma",
    "country_id": "34"
  }, {
    "id": "585",
    "name": "Houet",
    "country_id": "34"
  }, {
    "id": "586",
    "name": "Ioba",
    "country_id": "34"
  }, {
    "id": "587",
    "name": "Kadiogo",
    "country_id": "34"
  }, {
    "id": "588",
    "name": "Kenedougou",
    "country_id": "34"
  }, {
    "id": "589",
    "name": "Komandjari",
    "country_id": "34"
  }, {
    "id": "590",
    "name": "Kompienga",
    "country_id": "34"
  }, {
    "id": "591",
    "name": "Kossi",
    "country_id": "34"
  }, {
    "id": "592",
    "name": "Kouritenga",
    "country_id": "34"
  }, {
    "id": "593",
    "name": "Kourweogo",
    "country_id": "34"
  }, {
    "id": "594",
    "name": "Leraba",
    "country_id": "34"
  }, {
    "id": "595",
    "name": "Mouhoun",
    "country_id": "34"
  }, {
    "id": "596",
    "name": "Nahouri",
    "country_id": "34"
  }, {
    "id": "597",
    "name": "Namentenga",
    "country_id": "34"
  }, {
    "id": "598",
    "name": "Noumbiel",
    "country_id": "34"
  }, {
    "id": "599",
    "name": "Oubritenga",
    "country_id": "34"
  }, {
    "id": "600",
    "name": "Oudalan",
    "country_id": "34"
  }, {
    "id": "601",
    "name": "Passore",
    "country_id": "34"
  }, {
    "id": "602",
    "name": "Poni",
    "country_id": "34"
  }, {
    "id": "603",
    "name": "Sanguie",
    "country_id": "34"
  }, {
    "id": "604",
    "name": "Sanmatenga",
    "country_id": "34"
  }, {
    "id": "605",
    "name": "Seno",
    "country_id": "34"
  }, {
    "id": "606",
    "name": "Sissili",
    "country_id": "34"
  }, {
    "id": "607",
    "name": "Soum",
    "country_id": "34"
  }, {
    "id": "608",
    "name": "Sourou",
    "country_id": "34"
  }, {
    "id": "609",
    "name": "Tapoa",
    "country_id": "34"
  }, {
    "id": "610",
    "name": "Tuy",
    "country_id": "34"
  }, {
    "id": "611",
    "name": "Yatenga",
    "country_id": "34"
  }, {
    "id": "612",
    "name": "Zondoma",
    "country_id": "34"
  }, {
    "id": "613",
    "name": "Zoundweogo",
    "country_id": "34"
  }, {
    "id": "614",
    "name": "Bubanza",
    "country_id": "35"
  }, {
    "id": "615",
    "name": "Bujumbura",
    "country_id": "35"
  }, {
    "id": "616",
    "name": "Bururi",
    "country_id": "35"
  }, {
    "id": "617",
    "name": "Cankuzo",
    "country_id": "35"
  }, {
    "id": "618",
    "name": "Cibitoke",
    "country_id": "35"
  }, {
    "id": "619",
    "name": "Gitega",
    "country_id": "35"
  }, {
    "id": "620",
    "name": "Karuzi",
    "country_id": "35"
  }, {
    "id": "621",
    "name": "Kayanza",
    "country_id": "35"
  }, {
    "id": "622",
    "name": "Kirundo",
    "country_id": "35"
  }, {
    "id": "623",
    "name": "Makamba",
    "country_id": "35"
  }, {
    "id": "624",
    "name": "Muramvya",
    "country_id": "35"
  }, {
    "id": "625",
    "name": "Muyinga",
    "country_id": "35"
  }, {
    "id": "626",
    "name": "Ngozi",
    "country_id": "35"
  }, {
    "id": "627",
    "name": "Rutana",
    "country_id": "35"
  }, {
    "id": "628",
    "name": "Ruyigi",
    "country_id": "35"
  }, {
    "id": "629",
    "name": "Banteay Mean Chey",
    "country_id": "36"
  }, {
    "id": "630",
    "name": "Bat Dambang",
    "country_id": "36"
  }, {
    "id": "631",
    "name": "Kampong Cham",
    "country_id": "36"
  }, {
    "id": "632",
    "name": "Kampong Chhnang",
    "country_id": "36"
  }, {
    "id": "633",
    "name": "Kampong Spoeu",
    "country_id": "36"
  }, {
    "id": "634",
    "name": "Kampong Thum",
    "country_id": "36"
  }, {
    "id": "635",
    "name": "Kampot",
    "country_id": "36"
  }, {
    "id": "636",
    "name": "Kandal",
    "country_id": "36"
  }, {
    "id": "637",
    "name": "Kaoh Kong",
    "country_id": "36"
  }, {
    "id": "638",
    "name": "Kracheh",
    "country_id": "36"
  }, {
    "id": "639",
    "name": "Krong Kaeb",
    "country_id": "36"
  }, {
    "id": "640",
    "name": "Krong Pailin",
    "country_id": "36"
  }, {
    "id": "641",
    "name": "Krong Preah Sihanouk",
    "country_id": "36"
  }, {
    "id": "642",
    "name": "Mondol Kiri",
    "country_id": "36"
  }, {
    "id": "643",
    "name": "Otdar Mean Chey",
    "country_id": "36"
  }, {
    "id": "644",
    "name": "Phnum Penh",
    "country_id": "36"
  }, {
    "id": "645",
    "name": "Pousat",
    "country_id": "36"
  }, {
    "id": "646",
    "name": "Preah Vihear",
    "country_id": "36"
  }, {
    "id": "647",
    "name": "Prey Veaeng",
    "country_id": "36"
  }, {
    "id": "648",
    "name": "Rotanak Kiri",
    "country_id": "36"
  }, {
    "id": "649",
    "name": "Siem Reab",
    "country_id": "36"
  }, {
    "id": "650",
    "name": "Stueng Traeng",
    "country_id": "36"
  }, {
    "id": "651",
    "name": "Svay Rieng",
    "country_id": "36"
  }, {
    "id": "652",
    "name": "Takaev",
    "country_id": "36"
  }, {
    "id": "653",
    "name": "Adamaoua",
    "country_id": "37"
  }, {
    "id": "654",
    "name": "Centre",
    "country_id": "37"
  }, {
    "id": "655",
    "name": "Est",
    "country_id": "37"
  }, {
    "id": "656",
    "name": "Littoral",
    "country_id": "37"
  }, {
    "id": "657",
    "name": "Nord",
    "country_id": "37"
  }, {
    "id": "658",
    "name": "Nord Extreme",
    "country_id": "37"
  }, {
    "id": "659",
    "name": "Nordouest",
    "country_id": "37"
  }, {
    "id": "660",
    "name": "Ouest",
    "country_id": "37"
  }, {
    "id": "661",
    "name": "Sud",
    "country_id": "37"
  }, {
    "id": "662",
    "name": "Sudouest",
    "country_id": "37"
  }, {
    "id": "663",
    "name": "Alberta",
    "country_id": "38"
  }, {
    "id": "664",
    "name": "British Columbia",
    "country_id": "38"
  }, {
    "id": "665",
    "name": "Manitoba",
    "country_id": "38"
  }, {
    "id": "666",
    "name": "New Brunswick",
    "country_id": "38"
  }, {
    "id": "667",
    "name": "Newfoundland and Labrador",
    "country_id": "38"
  }, {
    "id": "668",
    "name": "Northwest Territories",
    "country_id": "38"
  }, {
    "id": "669",
    "name": "Nova Scotia",
    "country_id": "38"
  }, {
    "id": "670",
    "name": "Nunavut",
    "country_id": "38"
  }, {
    "id": "671",
    "name": "Ontario",
    "country_id": "38"
  }, {
    "id": "672",
    "name": "Prince Edward Island",
    "country_id": "38"
  }, {
    "id": "673",
    "name": "Quebec",
    "country_id": "38"
  }, {
    "id": "674",
    "name": "Saskatchewan",
    "country_id": "38"
  }, {
    "id": "675",
    "name": "Yukon",
    "country_id": "38"
  }, {
    "id": "676",
    "name": "Boavista",
    "country_id": "39"
  }, {
    "id": "677",
    "name": "Brava",
    "country_id": "39"
  }, {
    "id": "678",
    "name": "Fogo",
    "country_id": "39"
  }, {
    "id": "679",
    "name": "Maio",
    "country_id": "39"
  }, {
    "id": "680",
    "name": "Sal",
    "country_id": "39"
  }, {
    "id": "681",
    "name": "Santo Antao",
    "country_id": "39"
  }, {
    "id": "682",
    "name": "Sao Nicolau",
    "country_id": "39"
  }, {
    "id": "683",
    "name": "Sao Tiago",
    "country_id": "39"
  }, {
    "id": "684",
    "name": "Sao Vicente",
    "country_id": "39"
  }, {
    "id": "685",
    "name": "Grand Cayman",
    "country_id": "40"
  }, {
    "id": "686",
    "name": "Bamingui-Bangoran",
    "country_id": "41"
  }, {
    "id": "687",
    "name": "Bangui",
    "country_id": "41"
  }, {
    "id": "688",
    "name": "Basse-Kotto",
    "country_id": "41"
  }, {
    "id": "689",
    "name": "Haut-Mbomou",
    "country_id": "41"
  }, {
    "id": "690",
    "name": "Haute-Kotto",
    "country_id": "41"
  }, {
    "id": "691",
    "name": "Kemo",
    "country_id": "41"
  }, {
    "id": "692",
    "name": "Lobaye",
    "country_id": "41"
  }, {
    "id": "693",
    "name": "Mambere-Kadei",
    "country_id": "41"
  }, {
    "id": "694",
    "name": "Mbomou",
    "country_id": "41"
  }, {
    "id": "695",
    "name": "Nana-Gribizi",
    "country_id": "41"
  }, {
    "id": "696",
    "name": "Nana-Mambere",
    "country_id": "41"
  }, {
    "id": "697",
    "name": "Ombella Mpoko",
    "country_id": "41"
  }, {
    "id": "698",
    "name": "Ouaka",
    "country_id": "41"
  }, {
    "id": "699",
    "name": "Ouham",
    "country_id": "41"
  }, {
    "id": "700",
    "name": "Ouham-Pende",
    "country_id": "41"
  }, {
    "id": "701",
    "name": "Sangha-Mbaere",
    "country_id": "41"
  }, {
    "id": "702",
    "name": "Vakaga",
    "country_id": "41"
  }, {
    "id": "703",
    "name": "Batha",
    "country_id": "42"
  }, {
    "id": "704",
    "name": "Biltine",
    "country_id": "42"
  }, {
    "id": "705",
    "name": "Bourkou-Ennedi-Tibesti",
    "country_id": "42"
  }, {
    "id": "706",
    "name": "Chari-Baguirmi",
    "country_id": "42"
  }, {
    "id": "707",
    "name": "Guera",
    "country_id": "42"
  }, {
    "id": "708",
    "name": "Kanem",
    "country_id": "42"
  }, {
    "id": "709",
    "name": "Lac",
    "country_id": "42"
  }, {
    "id": "710",
    "name": "Logone Occidental",
    "country_id": "42"
  }, {
    "id": "711",
    "name": "Logone Oriental",
    "country_id": "42"
  }, {
    "id": "712",
    "name": "Mayo-Kebbi",
    "country_id": "42"
  }, {
    "id": "713",
    "name": "Moyen-Chari",
    "country_id": "42"
  }, {
    "id": "714",
    "name": "Ouaddai",
    "country_id": "42"
  }, {
    "id": "715",
    "name": "Salamat",
    "country_id": "42"
  }, {
    "id": "716",
    "name": "Tandjile",
    "country_id": "42"
  }, {
    "id": "717",
    "name": "Aisen",
    "country_id": "43"
  }, {
    "id": "718",
    "name": "Antofagasta",
    "country_id": "43"
  }, {
    "id": "719",
    "name": "Araucania",
    "country_id": "43"
  }, {
    "id": "720",
    "name": "Atacama",
    "country_id": "43"
  }, {
    "id": "721",
    "name": "Bio Bio",
    "country_id": "43"
  }, {
    "id": "722",
    "name": "Coquimbo",
    "country_id": "43"
  }, {
    "id": "723",
    "name": "Libertador General Bernardo O'",
    "country_id": "43"
  }, {
    "id": "724",
    "name": "Los Lagos",
    "country_id": "43"
  }, {
    "id": "725",
    "name": "Magellanes",
    "country_id": "43"
  }, {
    "id": "726",
    "name": "Maule",
    "country_id": "43"
  }, {
    "id": "727",
    "name": "Metropolitana",
    "country_id": "43"
  }, {
    "id": "728",
    "name": "Metropolitana de Santiago",
    "country_id": "43"
  }, {
    "id": "729",
    "name": "Tarapaca",
    "country_id": "43"
  }, {
    "id": "730",
    "name": "Valparaiso",
    "country_id": "43"
  }, {
    "id": "731",
    "name": "Anhui",
    "country_id": "44"
  }, {
    "id": "734",
    "name": "Aomen",
    "country_id": "44"
  }, {
    "id": "735",
    "name": "Beijing",
    "country_id": "44"
  }, {
    "id": "736",
    "name": "Beijing Shi",
    "country_id": "44"
  }, {
    "id": "737",
    "name": "Chongqing",
    "country_id": "44"
  }, {
    "id": "738",
    "name": "Fujian",
    "country_id": "44"
  }, {
    "id": "740",
    "name": "Gansu",
    "country_id": "44"
  }, {
    "id": "741",
    "name": "Guangdong",
    "country_id": "44"
  }, {
    "id": "743",
    "name": "Guangxi",
    "country_id": "44"
  }, {
    "id": "744",
    "name": "Guizhou",
    "country_id": "44"
  }, {
    "id": "745",
    "name": "Hainan",
    "country_id": "44"
  }, {
    "id": "746",
    "name": "Hebei",
    "country_id": "44"
  }, {
    "id": "747",
    "name": "Heilongjiang",
    "country_id": "44"
  }, {
    "id": "748",
    "name": "Henan",
    "country_id": "44"
  }, {
    "id": "749",
    "name": "Hubei",
    "country_id": "44"
  }, {
    "id": "750",
    "name": "Hunan",
    "country_id": "44"
  }, {
    "id": "751",
    "name": "Jiangsu",
    "country_id": "44"
  }, {
    "id": "753",
    "name": "Jiangxi",
    "country_id": "44"
  }, {
    "id": "754",
    "name": "Jilin",
    "country_id": "44"
  }, {
    "id": "755",
    "name": "Liaoning",
    "country_id": "44"
  }, {
    "id": "757",
    "name": "Nei Monggol",
    "country_id": "44"
  }, {
    "id": "758",
    "name": "Ningxia Hui",
    "country_id": "44"
  }, {
    "id": "759",
    "name": "Qinghai",
    "country_id": "44"
  }, {
    "id": "760",
    "name": "Shaanxi",
    "country_id": "44"
  }, {
    "id": "761",
    "name": "Shandong",
    "country_id": "44"
  }, {
    "id": "763",
    "name": "Shanghai",
    "country_id": "44"
  }, {
    "id": "764",
    "name": "Shanxi",
    "country_id": "44"
  }, {
    "id": "765",
    "name": "Sichuan",
    "country_id": "44"
  }, {
    "id": "766",
    "name": "Tianjin",
    "country_id": "44"
  }, {
    "id": "767",
    "name": "Xianggang",
    "country_id": "44"
  }, {
    "id": "768",
    "name": "Xinjiang",
    "country_id": "44"
  }, {
    "id": "769",
    "name": "Xizang",
    "country_id": "44"
  }, {
    "id": "770",
    "name": "Yunnan",
    "country_id": "44"
  }, {
    "id": "771",
    "name": "Zhejiang",
    "country_id": "44"
  }, {
    "id": "773",
    "name": "Christmas Island",
    "country_id": "45"
  }, {
    "id": "774",
    "name": "Cocos (Keeling) Islands",
    "country_id": "46"
  }, {
    "id": "775",
    "name": "Amazonas",
    "country_id": "47"
  }, {
    "id": "776",
    "name": "Antioquia",
    "country_id": "47"
  }, {
    "id": "777",
    "name": "Arauca",
    "country_id": "47"
  }, {
    "id": "778",
    "name": "Atlantico",
    "country_id": "47"
  }, {
    "id": "779",
    "name": "Bogota",
    "country_id": "47"
  }, {
    "id": "780",
    "name": "Bolivar",
    "country_id": "47"
  }, {
    "id": "781",
    "name": "Boyaca",
    "country_id": "47"
  }, {
    "id": "782",
    "name": "Caldas",
    "country_id": "47"
  }, {
    "id": "783",
    "name": "Caqueta",
    "country_id": "47"
  }, {
    "id": "784",
    "name": "Casanare",
    "country_id": "47"
  }, {
    "id": "785",
    "name": "Cauca",
    "country_id": "47"
  }, {
    "id": "786",
    "name": "Cesar",
    "country_id": "47"
  }, {
    "id": "787",
    "name": "Choco",
    "country_id": "47"
  }, {
    "id": "788",
    "name": "Cordoba",
    "country_id": "47"
  }, {
    "id": "789",
    "name": "Cundinamarca",
    "country_id": "47"
  }, {
    "id": "790",
    "name": "Guainia",
    "country_id": "47"
  }, {
    "id": "791",
    "name": "Guaviare",
    "country_id": "47"
  }, {
    "id": "792",
    "name": "Huila",
    "country_id": "47"
  }, {
    "id": "793",
    "name": "La Guajira",
    "country_id": "47"
  }, {
    "id": "794",
    "name": "Magdalena",
    "country_id": "47"
  }, {
    "id": "795",
    "name": "Meta",
    "country_id": "47"
  }, {
    "id": "796",
    "name": "Narino",
    "country_id": "47"
  }, {
    "id": "797",
    "name": "Norte de Santander",
    "country_id": "47"
  }, {
    "id": "798",
    "name": "Putumayo",
    "country_id": "47"
  }, {
    "id": "799",
    "name": "Quindio",
    "country_id": "47"
  }, {
    "id": "800",
    "name": "Risaralda",
    "country_id": "47"
  }, {
    "id": "801",
    "name": "San Andres y Providencia",
    "country_id": "47"
  }, {
    "id": "802",
    "name": "Santander",
    "country_id": "47"
  }, {
    "id": "803",
    "name": "Sucre",
    "country_id": "47"
  }, {
    "id": "804",
    "name": "Tolima",
    "country_id": "47"
  }, {
    "id": "805",
    "name": "Valle del Cauca",
    "country_id": "47"
  }, {
    "id": "806",
    "name": "Vaupes",
    "country_id": "47"
  }, {
    "id": "807",
    "name": "Vichada",
    "country_id": "47"
  }, {
    "id": "808",
    "name": "Mwali",
    "country_id": "48"
  }, {
    "id": "809",
    "name": "Njazidja",
    "country_id": "48"
  }, {
    "id": "810",
    "name": "Nzwani",
    "country_id": "48"
  }, {
    "id": "811",
    "name": "Bouenza",
    "country_id": "49"
  }, {
    "id": "812",
    "name": "Brazzaville",
    "country_id": "49"
  }, {
    "id": "813",
    "name": "Cuvette",
    "country_id": "49"
  }, {
    "id": "814",
    "name": "Kouilou",
    "country_id": "49"
  }, {
    "id": "815",
    "name": "Lekoumou",
    "country_id": "49"
  }, {
    "id": "816",
    "name": "Likouala",
    "country_id": "49"
  }, {
    "id": "817",
    "name": "Niari",
    "country_id": "49"
  }, {
    "id": "818",
    "name": "Plateaux",
    "country_id": "49"
  }, {
    "id": "819",
    "name": "Pool",
    "country_id": "49"
  }, {
    "id": "820",
    "name": "Sangha",
    "country_id": "49"
  }, {
    "id": "821",
    "name": "Bandundu",
    "country_id": "50"
  }, {
    "id": "822",
    "name": "Bas-Congo",
    "country_id": "50"
  }, {
    "id": "823",
    "name": "Equateur",
    "country_id": "50"
  }, {
    "id": "824",
    "name": "Haut-Congo",
    "country_id": "50"
  }, {
    "id": "825",
    "name": "Kasai-Occidental",
    "country_id": "50"
  }, {
    "id": "826",
    "name": "Kasai-Oriental",
    "country_id": "50"
  }, {
    "id": "827",
    "name": "Katanga",
    "country_id": "50"
  }, {
    "id": "828",
    "name": "Kinshasa",
    "country_id": "50"
  }, {
    "id": "829",
    "name": "Maniema",
    "country_id": "50"
  }, {
    "id": "830",
    "name": "Nord-Kivu",
    "country_id": "50"
  }, {
    "id": "831",
    "name": "Sud-Kivu",
    "country_id": "50"
  }, {
    "id": "832",
    "name": "Aitutaki",
    "country_id": "51"
  }, {
    "id": "833",
    "name": "Atiu",
    "country_id": "51"
  }, {
    "id": "834",
    "name": "Mangaia",
    "country_id": "51"
  }, {
    "id": "835",
    "name": "Manihiki",
    "country_id": "51"
  }, {
    "id": "836",
    "name": "Mauke",
    "country_id": "51"
  }, {
    "id": "837",
    "name": "Mitiaro",
    "country_id": "51"
  }, {
    "id": "838",
    "name": "Nassau",
    "country_id": "51"
  }, {
    "id": "839",
    "name": "Pukapuka",
    "country_id": "51"
  }, {
    "id": "840",
    "name": "Rakahanga",
    "country_id": "51"
  }, {
    "id": "841",
    "name": "Rarotonga",
    "country_id": "51"
  }, {
    "id": "842",
    "name": "Tongareva",
    "country_id": "51"
  }, {
    "id": "843",
    "name": "Alajuela",
    "country_id": "52"
  }, {
    "id": "844",
    "name": "Cartago",
    "country_id": "52"
  }, {
    "id": "845",
    "name": "Guanacaste",
    "country_id": "52"
  }, {
    "id": "846",
    "name": "Heredia",
    "country_id": "52"
  }, {
    "id": "847",
    "name": "Limon",
    "country_id": "52"
  }, {
    "id": "848",
    "name": "Puntarenas",
    "country_id": "52"
  }, {
    "id": "849",
    "name": "San Jose",
    "country_id": "52"
  }, {
    "id": "850",
    "name": "Abidjan",
    "country_id": "53"
  }, {
    "id": "851",
    "name": "Agneby",
    "country_id": "53"
  }, {
    "id": "852",
    "name": "Bafing",
    "country_id": "53"
  }, {
    "id": "853",
    "name": "Denguele",
    "country_id": "53"
  }, {
    "id": "854",
    "name": "Dix-huit Montagnes",
    "country_id": "53"
  }, {
    "id": "855",
    "name": "Fromager",
    "country_id": "53"
  }, {
    "id": "856",
    "name": "Haut-Sassandra",
    "country_id": "53"
  }, {
    "id": "857",
    "name": "Lacs",
    "country_id": "53"
  }, {
    "id": "858",
    "name": "Lagunes",
    "country_id": "53"
  }, {
    "id": "859",
    "name": "Marahoue",
    "country_id": "53"
  }, {
    "id": "860",
    "name": "Moyen-Cavally",
    "country_id": "53"
  }, {
    "id": "861",
    "name": "Moyen-Comoe",
    "country_id": "53"
  }, {
    "id": "862",
    "name": "N'zi-Comoe",
    "country_id": "53"
  }, {
    "id": "863",
    "name": "Sassandra",
    "country_id": "53"
  }, {
    "id": "864",
    "name": "Savanes",
    "country_id": "53"
  }, {
    "id": "865",
    "name": "Sud-Bandama",
    "country_id": "53"
  }, {
    "id": "866",
    "name": "Sud-Comoe",
    "country_id": "53"
  }, {
    "id": "867",
    "name": "Vallee du Bandama",
    "country_id": "53"
  }, {
    "id": "868",
    "name": "Worodougou",
    "country_id": "53"
  }, {
    "id": "869",
    "name": "Zanzan",
    "country_id": "53"
  }, {
    "id": "870",
    "name": "Bjelovar-Bilogora",
    "country_id": "54"
  }, {
    "id": "871",
    "name": "Dubrovnik-Neretva",
    "country_id": "54"
  }, {
    "id": "872",
    "name": "Grad Zagreb",
    "country_id": "54"
  }, {
    "id": "873",
    "name": "Istra",
    "country_id": "54"
  }, {
    "id": "874",
    "name": "Karlovac",
    "country_id": "54"
  }, {
    "id": "875",
    "name": "Koprivnica-Krizhevci",
    "country_id": "54"
  }, {
    "id": "876",
    "name": "Krapina-Zagorje",
    "country_id": "54"
  }, {
    "id": "877",
    "name": "Lika-Senj",
    "country_id": "54"
  }, {
    "id": "878",
    "name": "Medhimurje",
    "country_id": "54"
  }, {
    "id": "879",
    "name": "Medimurska Zupanija",
    "country_id": "54"
  }, {
    "id": "880",
    "name": "Osijek-Baranja",
    "country_id": "54"
  }, {
    "id": "881",
    "name": "Osjecko-Baranjska Zupanija",
    "country_id": "54"
  }, {
    "id": "882",
    "name": "Pozhega-Slavonija",
    "country_id": "54"
  }, {
    "id": "883",
    "name": "Primorje-Gorski Kotar",
    "country_id": "54"
  }, {
    "id": "884",
    "name": "Shibenik-Knin",
    "country_id": "54"
  }, {
    "id": "885",
    "name": "Sisak-Moslavina",
    "country_id": "54"
  }, {
    "id": "886",
    "name": "Slavonski Brod-Posavina",
    "country_id": "54"
  }, {
    "id": "887",
    "name": "Split-Dalmacija",
    "country_id": "54"
  }, {
    "id": "888",
    "name": "Varazhdin",
    "country_id": "54"
  }, {
    "id": "889",
    "name": "Virovitica-Podravina",
    "country_id": "54"
  }, {
    "id": "890",
    "name": "Vukovar-Srijem",
    "country_id": "54"
  }, {
    "id": "891",
    "name": "Zadar",
    "country_id": "54"
  }, {
    "id": "892",
    "name": "Zagreb",
    "country_id": "54"
  }, {
    "id": "893",
    "name": "Camaguey",
    "country_id": "55"
  }, {
    "id": "894",
    "name": "Ciego de Avila",
    "country_id": "55"
  }, {
    "id": "895",
    "name": "Cienfuegos",
    "country_id": "55"
  }, {
    "id": "896",
    "name": "Ciudad de la Habana",
    "country_id": "55"
  }, {
    "id": "897",
    "name": "Granma",
    "country_id": "55"
  }, {
    "id": "898",
    "name": "Guantanamo",
    "country_id": "55"
  }, {
    "id": "899",
    "name": "Habana",
    "country_id": "55"
  }, {
    "id": "900",
    "name": "Holguin",
    "country_id": "55"
  }, {
    "id": "901",
    "name": "Isla de la Juventud",
    "country_id": "55"
  }, {
    "id": "902",
    "name": "La Habana",
    "country_id": "55"
  }, {
    "id": "903",
    "name": "Las Tunas",
    "country_id": "55"
  }, {
    "id": "904",
    "name": "Matanzas",
    "country_id": "55"
  }, {
    "id": "905",
    "name": "Pinar del Rio",
    "country_id": "55"
  }, {
    "id": "906",
    "name": "Sancti Spiritus",
    "country_id": "55"
  }, {
    "id": "907",
    "name": "Santiago de Cuba",
    "country_id": "55"
  }, {
    "id": "908",
    "name": "Villa Clara",
    "country_id": "55"
  }, {
    "id": "909",
    "name": "Government controlled area",
    "country_id": "56"
  }, {
    "id": "910",
    "name": "Limassol",
    "country_id": "56"
  }, {
    "id": "911",
    "name": "Nicosia District",
    "country_id": "56"
  }, {
    "id": "912",
    "name": "Paphos",
    "country_id": "56"
  }, {
    "id": "913",
    "name": "Turkish controlled area",
    "country_id": "56"
  }, {
    "id": "914",
    "name": "Central Bohemian",
    "country_id": "57"
  }, {
    "id": "915",
    "name": "Frycovice",
    "country_id": "57"
  }, {
    "id": "916",
    "name": "Jihocesky Kraj",
    "country_id": "57"
  }, {
    "id": "917",
    "name": "Jihochesky",
    "country_id": "57"
  }, {
    "id": "918",
    "name": "Jihomoravsky",
    "country_id": "57"
  }, {
    "id": "919",
    "name": "Karlovarsky",
    "country_id": "57"
  }, {
    "id": "920",
    "name": "Klecany",
    "country_id": "57"
  }, {
    "id": "921",
    "name": "Kralovehradecky",
    "country_id": "57"
  }, {
    "id": "922",
    "name": "Liberecky",
    "country_id": "57"
  }, {
    "id": "923",
    "name": "Lipov",
    "country_id": "57"
  }, {
    "id": "924",
    "name": "Moravskoslezsky",
    "country_id": "57"
  }, {
    "id": "925",
    "name": "Olomoucky",
    "country_id": "57"
  }, {
    "id": "926",
    "name": "Olomoucky Kraj",
    "country_id": "57"
  }, {
    "id": "927",
    "name": "Pardubicky",
    "country_id": "57"
  }, {
    "id": "928",
    "name": "Plzensky",
    "country_id": "57"
  }, {
    "id": "929",
    "name": "Praha",
    "country_id": "57"
  }, {
    "id": "930",
    "name": "Rajhrad",
    "country_id": "57"
  }, {
    "id": "931",
    "name": "Smirice",
    "country_id": "57"
  }, {
    "id": "932",
    "name": "South Moravian",
    "country_id": "57"
  }, {
    "id": "933",
    "name": "Straz nad Nisou",
    "country_id": "57"
  }, {
    "id": "934",
    "name": "Stredochesky",
    "country_id": "57"
  }, {
    "id": "935",
    "name": "Unicov",
    "country_id": "57"
  }, {
    "id": "936",
    "name": "Ustecky",
    "country_id": "57"
  }, {
    "id": "937",
    "name": "Valletta",
    "country_id": "57"
  }, {
    "id": "938",
    "name": "Velesin",
    "country_id": "57"
  }, {
    "id": "939",
    "name": "Vysochina",
    "country_id": "57"
  }, {
    "id": "940",
    "name": "Zlinsky",
    "country_id": "57"
  }, {
    "id": "941",
    "name": "Arhus",
    "country_id": "58"
  }, {
    "id": "942",
    "name": "Bornholm",
    "country_id": "58"
  }, {
    "id": "943",
    "name": "Frederiksborg",
    "country_id": "58"
  }, {
    "id": "944",
    "name": "Fyn",
    "country_id": "58"
  }, {
    "id": "945",
    "name": "Hovedstaden",
    "country_id": "58"
  }, {
    "id": "946",
    "name": "Kobenhavn",
    "country_id": "58"
  }, {
    "id": "947",
    "name": "Kobenhavns Amt",
    "country_id": "58"
  }, {
    "id": "948",
    "name": "Kobenhavns Kommune",
    "country_id": "58"
  }, {
    "id": "949",
    "name": "Nordjylland",
    "country_id": "58"
  }, {
    "id": "950",
    "name": "Ribe",
    "country_id": "58"
  }, {
    "id": "951",
    "name": "Ringkobing",
    "country_id": "58"
  }, {
    "id": "952",
    "name": "Roervig",
    "country_id": "58"
  }, {
    "id": "953",
    "name": "Roskilde",
    "country_id": "58"
  }, {
    "id": "954",
    "name": "Roslev",
    "country_id": "58"
  }, {
    "id": "955",
    "name": "Sjaelland",
    "country_id": "58"
  }, {
    "id": "956",
    "name": "Soeborg",
    "country_id": "58"
  }, {
    "id": "957",
    "name": "Sonderjylland",
    "country_id": "58"
  }, {
    "id": "958",
    "name": "Storstrom",
    "country_id": "58"
  }, {
    "id": "959",
    "name": "Syddanmark",
    "country_id": "58"
  }, {
    "id": "960",
    "name": "Toelloese",
    "country_id": "58"
  }, {
    "id": "961",
    "name": "Vejle",
    "country_id": "58"
  }, {
    "id": "962",
    "name": "Vestsjalland",
    "country_id": "58"
  }, {
    "id": "963",
    "name": "Viborg",
    "country_id": "58"
  }, {
    "id": "964",
    "name": "'Ali Sabih",
    "country_id": "59"
  }, {
    "id": "965",
    "name": "Dikhil",
    "country_id": "59"
  }, {
    "id": "966",
    "name": "Jibuti",
    "country_id": "59"
  }, {
    "id": "967",
    "name": "Tajurah",
    "country_id": "59"
  }, {
    "id": "968",
    "name": "Ubuk",
    "country_id": "59"
  }, {
    "id": "969",
    "name": "Saint Andrew",
    "country_id": "60"
  }, {
    "id": "970",
    "name": "Saint David",
    "country_id": "60"
  }, {
    "id": "971",
    "name": "Saint George",
    "country_id": "60"
  }, {
    "id": "972",
    "name": "Saint John",
    "country_id": "60"
  }, {
    "id": "973",
    "name": "Saint Joseph",
    "country_id": "60"
  }, {
    "id": "974",
    "name": "Saint Luke",
    "country_id": "60"
  }, {
    "id": "975",
    "name": "Saint Mark",
    "country_id": "60"
  }, {
    "id": "976",
    "name": "Saint Patrick",
    "country_id": "60"
  }, {
    "id": "977",
    "name": "Saint Paul",
    "country_id": "60"
  }, {
    "id": "978",
    "name": "Saint Peter",
    "country_id": "60"
  }, {
    "id": "979",
    "name": "Azua",
    "country_id": "61"
  }, {
    "id": "980",
    "name": "Bahoruco",
    "country_id": "61"
  }, {
    "id": "981",
    "name": "Barahona",
    "country_id": "61"
  }, {
    "id": "982",
    "name": "Dajabon",
    "country_id": "61"
  }, {
    "id": "983",
    "name": "Distrito Nacional",
    "country_id": "61"
  }, {
    "id": "984",
    "name": "Duarte",
    "country_id": "61"
  }, {
    "id": "985",
    "name": "El Seybo",
    "country_id": "61"
  }, {
    "id": "986",
    "name": "Elias Pina",
    "country_id": "61"
  }, {
    "id": "987",
    "name": "Espaillat",
    "country_id": "61"
  }, {
    "id": "988",
    "name": "Hato Mayor",
    "country_id": "61"
  }, {
    "id": "989",
    "name": "Independencia",
    "country_id": "61"
  }, {
    "id": "990",
    "name": "La Altagracia",
    "country_id": "61"
  }, {
    "id": "991",
    "name": "La Romana",
    "country_id": "61"
  }, {
    "id": "992",
    "name": "La Vega",
    "country_id": "61"
  }, {
    "id": "993",
    "name": "Maria Trinidad Sanchez",
    "country_id": "61"
  }, {
    "id": "994",
    "name": "Monsenor Nouel",
    "country_id": "61"
  }, {
    "id": "995",
    "name": "Monte Cristi",
    "country_id": "61"
  }, {
    "id": "996",
    "name": "Monte Plata",
    "country_id": "61"
  }, {
    "id": "997",
    "name": "Pedernales",
    "country_id": "61"
  }, {
    "id": "998",
    "name": "Peravia",
    "country_id": "61"
  }, {
    "id": "999",
    "name": "Puerto Plata",
    "country_id": "61"
  }, {
    "id": "1000",
    "name": "Salcedo",
    "country_id": "61"
  }, {
    "id": "1001",
    "name": "Samana",
    "country_id": "61"
  }, {
    "id": "1002",
    "name": "San Cristobal",
    "country_id": "61"
  }, {
    "id": "1003",
    "name": "San Juan",
    "country_id": "61"
  }, {
    "id": "1004",
    "name": "San Pedro de Macoris",
    "country_id": "61"
  }, {
    "id": "1005",
    "name": "Sanchez Ramirez",
    "country_id": "61"
  }, {
    "id": "1006",
    "name": "Santiago",
    "country_id": "61"
  }, {
    "id": "1007",
    "name": "Santiago Rodriguez",
    "country_id": "61"
  }, {
    "id": "1008",
    "name": "Valverde",
    "country_id": "61"
  }, {
    "id": "1009",
    "name": "Aileu",
    "country_id": "62"
  }, {
    "id": "1010",
    "name": "Ainaro",
    "country_id": "62"
  }, {
    "id": "1011",
    "name": "Ambeno",
    "country_id": "62"
  }, {
    "id": "1012",
    "name": "Baucau",
    "country_id": "62"
  }, {
    "id": "1013",
    "name": "Bobonaro",
    "country_id": "62"
  }, {
    "id": "1014",
    "name": "Cova Lima",
    "country_id": "62"
  }, {
    "id": "1015",
    "name": "Dili",
    "country_id": "62"
  }, {
    "id": "1016",
    "name": "Ermera",
    "country_id": "62"
  }, {
    "id": "1017",
    "name": "Lautem",
    "country_id": "62"
  }, {
    "id": "1018",
    "name": "Liquica",
    "country_id": "62"
  }, {
    "id": "1019",
    "name": "Manatuto",
    "country_id": "62"
  }, {
    "id": "1020",
    "name": "Manufahi",
    "country_id": "62"
  }, {
    "id": "1021",
    "name": "Viqueque",
    "country_id": "62"
  }, {
    "id": "1022",
    "name": "Azuay",
    "country_id": "63"
  }, {
    "id": "1023",
    "name": "Bolivar",
    "country_id": "63"
  }, {
    "id": "1024",
    "name": "Canar",
    "country_id": "63"
  }, {
    "id": "1025",
    "name": "Carchi",
    "country_id": "63"
  }, {
    "id": "1026",
    "name": "Chimborazo",
    "country_id": "63"
  }, {
    "id": "1027",
    "name": "Cotopaxi",
    "country_id": "63"
  }, {
    "id": "1028",
    "name": "El Oro",
    "country_id": "63"
  }, {
    "id": "1029",
    "name": "Esmeraldas",
    "country_id": "63"
  }, {
    "id": "1030",
    "name": "Galapagos",
    "country_id": "63"
  }, {
    "id": "1031",
    "name": "Guayas",
    "country_id": "63"
  }, {
    "id": "1032",
    "name": "Imbabura",
    "country_id": "63"
  }, {
    "id": "1033",
    "name": "Loja",
    "country_id": "63"
  }, {
    "id": "1034",
    "name": "Los Rios",
    "country_id": "63"
  }, {
    "id": "1035",
    "name": "Manabi",
    "country_id": "63"
  }, {
    "id": "1036",
    "name": "Morona Santiago",
    "country_id": "63"
  }, {
    "id": "1037",
    "name": "Napo",
    "country_id": "63"
  }, {
    "id": "1038",
    "name": "Orellana",
    "country_id": "63"
  }, {
    "id": "1039",
    "name": "Pastaza",
    "country_id": "63"
  }, {
    "id": "1040",
    "name": "Pichincha",
    "country_id": "63"
  }, {
    "id": "1041",
    "name": "Sucumbios",
    "country_id": "63"
  }, {
    "id": "1042",
    "name": "Tungurahua",
    "country_id": "63"
  }, {
    "id": "1043",
    "name": "Zamora Chinchipe",
    "country_id": "63"
  }, {
    "id": "1044",
    "name": "Aswan",
    "country_id": "64"
  }, {
    "id": "1045",
    "name": "Asyut",
    "country_id": "64"
  }, {
    "id": "1046",
    "name": "Bani Suwayf",
    "country_id": "64"
  }, {
    "id": "1047",
    "name": "Bur Sa'id",
    "country_id": "64"
  }, {
    "id": "1048",
    "name": "Cairo",
    "country_id": "64"
  }, {
    "id": "1049",
    "name": "Dumyat",
    "country_id": "64"
  }, {
    "id": "1050",
    "name": "Kafr-ash-Shaykh",
    "country_id": "64"
  }, {
    "id": "1051",
    "name": "Matruh",
    "country_id": "64"
  }, {
    "id": "1052",
    "name": "Muhafazat ad Daqahliyah",
    "country_id": "64"
  }, {
    "id": "1053",
    "name": "Muhafazat al Fayyum",
    "country_id": "64"
  }, {
    "id": "1054",
    "name": "Muhafazat al Gharbiyah",
    "country_id": "64"
  }, {
    "id": "1055",
    "name": "Muhafazat al Iskandariyah",
    "country_id": "64"
  }, {
    "id": "1056",
    "name": "Muhafazat al Qahirah",
    "country_id": "64"
  }, {
    "id": "1057",
    "name": "Qina",
    "country_id": "64"
  }, {
    "id": "1058",
    "name": "Sawhaj",
    "country_id": "64"
  }, {
    "id": "1059",
    "name": "Sina al-Janubiyah",
    "country_id": "64"
  }, {
    "id": "1060",
    "name": "Sina ash-Shamaliyah",
    "country_id": "64"
  }, {
    "id": "1061",
    "name": "ad-Daqahliyah",
    "country_id": "64"
  }, {
    "id": "1062",
    "name": "al-Bahr-al-Ahmar",
    "country_id": "64"
  }, {
    "id": "1063",
    "name": "al-Buhayrah",
    "country_id": "64"
  }, {
    "id": "1064",
    "name": "al-Fayyum",
    "country_id": "64"
  }, {
    "id": "1065",
    "name": "al-Gharbiyah",
    "country_id": "64"
  }, {
    "id": "1066",
    "name": "al-Iskandariyah",
    "country_id": "64"
  }, {
    "id": "1067",
    "name": "al-Ismailiyah",
    "country_id": "64"
  }, {
    "id": "1068",
    "name": "al-Jizah",
    "country_id": "64"
  }, {
    "id": "1069",
    "name": "al-Minufiyah",
    "country_id": "64"
  }, {
    "id": "1070",
    "name": "al-Minya",
    "country_id": "64"
  }, {
    "id": "1071",
    "name": "al-Qahira",
    "country_id": "64"
  }, {
    "id": "1072",
    "name": "al-Qalyubiyah",
    "country_id": "64"
  }, {
    "id": "1073",
    "name": "al-Uqsur",
    "country_id": "64"
  }, {
    "id": "1074",
    "name": "al-Wadi al-Jadid",
    "country_id": "64"
  }, {
    "id": "1075",
    "name": "as-Suways",
    "country_id": "64"
  }, {
    "id": "1076",
    "name": "ash-Sharqiyah",
    "country_id": "64"
  }, {
    "id": "1077",
    "name": "Ahuachapan",
    "country_id": "65"
  }, {
    "id": "1078",
    "name": "Cabanas",
    "country_id": "65"
  }, {
    "id": "1079",
    "name": "Chalatenango",
    "country_id": "65"
  }, {
    "id": "1080",
    "name": "Cuscatlan",
    "country_id": "65"
  }, {
    "id": "1081",
    "name": "La Libertad",
    "country_id": "65"
  }, {
    "id": "1082",
    "name": "La Paz",
    "country_id": "65"
  }, {
    "id": "1083",
    "name": "La Union",
    "country_id": "65"
  }, {
    "id": "1084",
    "name": "Morazan",
    "country_id": "65"
  }, {
    "id": "1085",
    "name": "San Miguel",
    "country_id": "65"
  }, {
    "id": "1086",
    "name": "San Salvador",
    "country_id": "65"
  }, {
    "id": "1087",
    "name": "San Vicente",
    "country_id": "65"
  }, {
    "id": "1088",
    "name": "Santa Ana",
    "country_id": "65"
  }, {
    "id": "1089",
    "name": "Sonsonate",
    "country_id": "65"
  }, {
    "id": "1090",
    "name": "Usulutan",
    "country_id": "65"
  }, {
    "id": "1091",
    "name": "Annobon",
    "country_id": "66"
  }, {
    "id": "1092",
    "name": "Bioko Norte",
    "country_id": "66"
  }, {
    "id": "1093",
    "name": "Bioko Sur",
    "country_id": "66"
  }, {
    "id": "1094",
    "name": "Centro Sur",
    "country_id": "66"
  }, {
    "id": "1095",
    "name": "Kie-Ntem",
    "country_id": "66"
  }, {
    "id": "1096",
    "name": "Litoral",
    "country_id": "66"
  }, {
    "id": "1097",
    "name": "Wele-Nzas",
    "country_id": "66"
  }, {
    "id": "1098",
    "name": "Anseba",
    "country_id": "67"
  }, {
    "id": "1099",
    "name": "Debub",
    "country_id": "67"
  }, {
    "id": "1100",
    "name": "Debub-Keih-Bahri",
    "country_id": "67"
  }, {
    "id": "1101",
    "name": "Gash-Barka",
    "country_id": "67"
  }, {
    "id": "1102",
    "name": "Maekel",
    "country_id": "67"
  }, {
    "id": "1103",
    "name": "Semien-Keih-Bahri",
    "country_id": "67"
  }, {
    "id": "1104",
    "name": "Harju",
    "country_id": "68"
  }, {
    "id": "1105",
    "name": "Hiiu",
    "country_id": "68"
  }, {
    "id": "1106",
    "name": "Ida-Viru",
    "country_id": "68"
  }, {
    "id": "1107",
    "name": "Jarva",
    "country_id": "68"
  }, {
    "id": "1108",
    "name": "Jogeva",
    "country_id": "68"
  }, {
    "id": "1109",
    "name": "Laane",
    "country_id": "68"
  }, {
    "id": "1110",
    "name": "Laane-Viru",
    "country_id": "68"
  }, {
    "id": "1111",
    "name": "Parnu",
    "country_id": "68"
  }, {
    "id": "1112",
    "name": "Polva",
    "country_id": "68"
  }, {
    "id": "1113",
    "name": "Rapla",
    "country_id": "68"
  }, {
    "id": "1114",
    "name": "Saare",
    "country_id": "68"
  }, {
    "id": "1115",
    "name": "Tartu",
    "country_id": "68"
  }, {
    "id": "1116",
    "name": "Valga",
    "country_id": "68"
  }, {
    "id": "1117",
    "name": "Viljandi",
    "country_id": "68"
  }, {
    "id": "1118",
    "name": "Voru",
    "country_id": "68"
  }, {
    "id": "1119",
    "name": "Addis Abeba",
    "country_id": "69"
  }, {
    "id": "1120",
    "name": "Afar",
    "country_id": "69"
  }, {
    "id": "1121",
    "name": "Amhara",
    "country_id": "69"
  }, {
    "id": "1122",
    "name": "Benishangul",
    "country_id": "69"
  }, {
    "id": "1123",
    "name": "Diredawa",
    "country_id": "69"
  }, {
    "id": "1124",
    "name": "Gambella",
    "country_id": "69"
  }, {
    "id": "1125",
    "name": "Harar",
    "country_id": "69"
  }, {
    "id": "1126",
    "name": "Jigjiga",
    "country_id": "69"
  }, {
    "id": "1127",
    "name": "Mekele",
    "country_id": "69"
  }, {
    "id": "1128",
    "name": "Oromia",
    "country_id": "69"
  }, {
    "id": "1129",
    "name": "Somali",
    "country_id": "69"
  }, {
    "id": "1130",
    "name": "Southern",
    "country_id": "69"
  }, {
    "id": "1131",
    "name": "Tigray",
    "country_id": "69"
  }, {
    "id": "1132",
    "name": "Christmas Island",
    "country_id": "70"
  }, {
    "id": "1133",
    "name": "Cocos Islands",
    "country_id": "70"
  }, {
    "id": "1134",
    "name": "Coral Sea Islands",
    "country_id": "70"
  }, {
    "id": "1135",
    "name": "Falkland Islands",
    "country_id": "71"
  }, {
    "id": "1136",
    "name": "South Georgia",
    "country_id": "71"
  }, {
    "id": "1137",
    "name": "Klaksvik",
    "country_id": "72"
  }, {
    "id": "1138",
    "name": "Nor ara Eysturoy",
    "country_id": "72"
  }, {
    "id": "1139",
    "name": "Nor oy",
    "country_id": "72"
  }, {
    "id": "1140",
    "name": "Sandoy",
    "country_id": "72"
  }, {
    "id": "1141",
    "name": "Streymoy",
    "country_id": "72"
  }, {
    "id": "1142",
    "name": "Su uroy",
    "country_id": "72"
  }, {
    "id": "1143",
    "name": "Sy ra Eysturoy",
    "country_id": "72"
  }, {
    "id": "1144",
    "name": "Torshavn",
    "country_id": "72"
  }, {
    "id": "1145",
    "name": "Vaga",
    "country_id": "72"
  }, {
    "id": "1146",
    "name": "Central",
    "country_id": "73"
  }, {
    "id": "1147",
    "name": "Eastern",
    "country_id": "73"
  }, {
    "id": "1148",
    "name": "Northern",
    "country_id": "73"
  }, {
    "id": "1149",
    "name": "South Pacific",
    "country_id": "73"
  }, {
    "id": "1150",
    "name": "Western",
    "country_id": "73"
  }, {
    "id": "1151",
    "name": "Ahvenanmaa",
    "country_id": "74"
  }, {
    "id": "1152",
    "name": "Etela-Karjala",
    "country_id": "74"
  }, {
    "id": "1153",
    "name": "Etela-Pohjanmaa",
    "country_id": "74"
  }, {
    "id": "1154",
    "name": "Etela-Savo",
    "country_id": "74"
  }, {
    "id": "1155",
    "name": "Etela-Suomen Laani",
    "country_id": "74"
  }, {
    "id": "1156",
    "name": "Ita-Suomen Laani",
    "country_id": "74"
  }, {
    "id": "1157",
    "name": "Ita-Uusimaa",
    "country_id": "74"
  }, {
    "id": "1158",
    "name": "Kainuu",
    "country_id": "74"
  }, {
    "id": "1159",
    "name": "Kanta-Hame",
    "country_id": "74"
  }, {
    "id": "1160",
    "name": "Keski-Pohjanmaa",
    "country_id": "74"
  }, {
    "id": "1161",
    "name": "Keski-Suomi",
    "country_id": "74"
  }, {
    "id": "1162",
    "name": "Kymenlaakso",
    "country_id": "74"
  }, {
    "id": "1163",
    "name": "Lansi-Suomen Laani",
    "country_id": "74"
  }, {
    "id": "1164",
    "name": "Lappi",
    "country_id": "74"
  }, {
    "id": "1165",
    "name": "Northern Savonia",
    "country_id": "74"
  }, {
    "id": "1166",
    "name": "Ostrobothnia",
    "country_id": "74"
  }, {
    "id": "1167",
    "name": "Oulun Laani",
    "country_id": "74"
  }, {
    "id": "1168",
    "name": "Paijat-Hame",
    "country_id": "74"
  }, {
    "id": "1169",
    "name": "Pirkanmaa",
    "country_id": "74"
  }, {
    "id": "1170",
    "name": "Pohjanmaa",
    "country_id": "74"
  }, {
    "id": "1171",
    "name": "Pohjois-Karjala",
    "country_id": "74"
  }, {
    "id": "1172",
    "name": "Pohjois-Pohjanmaa",
    "country_id": "74"
  }, {
    "id": "1173",
    "name": "Pohjois-Savo",
    "country_id": "74"
  }, {
    "id": "1174",
    "name": "Saarijarvi",
    "country_id": "74"
  }, {
    "id": "1175",
    "name": "Satakunta",
    "country_id": "74"
  }, {
    "id": "1176",
    "name": "Southern Savonia",
    "country_id": "74"
  }, {
    "id": "1177",
    "name": "Tavastia Proper",
    "country_id": "74"
  }, {
    "id": "1178",
    "name": "Uleaborgs Lan",
    "country_id": "74"
  }, {
    "id": "1179",
    "name": "Uusimaa",
    "country_id": "74"
  }, {
    "id": "1180",
    "name": "Varsinais-Suomi",
    "country_id": "74"
  }, {
    "id": "1181",
    "name": "Ain",
    "country_id": "75"
  }, {
    "id": "1182",
    "name": "Aisne",
    "country_id": "75"
  }, {
    "id": "1183",
    "name": "Albi Le Sequestre",
    "country_id": "75"
  }, {
    "id": "1184",
    "name": "Allier",
    "country_id": "75"
  }, {
    "id": "1185",
    "name": "Alpes-Cote dAzur",
    "country_id": "75"
  }, {
    "id": "1186",
    "name": "Alpes-Maritimes",
    "country_id": "75"
  }, {
    "id": "1187",
    "name": "Alpes-de-Haute-Provence",
    "country_id": "75"
  }, {
    "id": "1188",
    "name": "Alsace",
    "country_id": "75"
  }, {
    "id": "1189",
    "name": "Aquitaine",
    "country_id": "75"
  }, {
    "id": "1190",
    "name": "Ardeche",
    "country_id": "75"
  }, {
    "id": "1191",
    "name": "Ardennes",
    "country_id": "75"
  }, {
    "id": "1192",
    "name": "Ariege",
    "country_id": "75"
  }, {
    "id": "1193",
    "name": "Aube",
    "country_id": "75"
  }, {
    "id": "1194",
    "name": "Aude",
    "country_id": "75"
  }, {
    "id": "1195",
    "name": "Auvergne",
    "country_id": "75"
  }, {
    "id": "1196",
    "name": "Aveyron",
    "country_id": "75"
  }, {
    "id": "1197",
    "name": "Bas-Rhin",
    "country_id": "75"
  }, {
    "id": "1198",
    "name": "Basse-Normandie",
    "country_id": "75"
  }, {
    "id": "1199",
    "name": "Bouches-du-Rhone",
    "country_id": "75"
  }, {
    "id": "1200",
    "name": "Bourgogne",
    "country_id": "75"
  }, {
    "id": "1201",
    "name": "Bretagne",
    "country_id": "75"
  }, {
    "id": "1202",
    "name": "Brittany",
    "country_id": "75"
  }, {
    "id": "1203",
    "name": "Burgundy",
    "country_id": "75"
  }, {
    "id": "1204",
    "name": "Calvados",
    "country_id": "75"
  }, {
    "id": "1205",
    "name": "Cantal",
    "country_id": "75"
  }, {
    "id": "1206",
    "name": "Cedex",
    "country_id": "75"
  }, {
    "id": "1207",
    "name": "Centre",
    "country_id": "75"
  }, {
    "id": "1208",
    "name": "Charente",
    "country_id": "75"
  }, {
    "id": "1209",
    "name": "Charente-Maritime",
    "country_id": "75"
  }, {
    "id": "1210",
    "name": "Cher",
    "country_id": "75"
  }, {
    "id": "1211",
    "name": "Correze",
    "country_id": "75"
  }, {
    "id": "1212",
    "name": "Corse-du-Sud",
    "country_id": "75"
  }, {
    "id": "1213",
    "name": "Cote-d'Or",
    "country_id": "75"
  }, {
    "id": "1214",
    "name": "Cotes-d'Armor",
    "country_id": "75"
  }, {
    "id": "1215",
    "name": "Creuse",
    "country_id": "75"
  }, {
    "id": "1216",
    "name": "Crolles",
    "country_id": "75"
  }, {
    "id": "1217",
    "name": "Deux-Sevres",
    "country_id": "75"
  }, {
    "id": "1218",
    "name": "Dordogne",
    "country_id": "75"
  }, {
    "id": "1219",
    "name": "Doubs",
    "country_id": "75"
  }, {
    "id": "1220",
    "name": "Drome",
    "country_id": "75"
  }, {
    "id": "1221",
    "name": "Essonne",
    "country_id": "75"
  }, {
    "id": "1222",
    "name": "Eure",
    "country_id": "75"
  }, {
    "id": "1223",
    "name": "Eure-et-Loir",
    "country_id": "75"
  }, {
    "id": "1224",
    "name": "Feucherolles",
    "country_id": "75"
  }, {
    "id": "1225",
    "name": "Finistere",
    "country_id": "75"
  }, {
    "id": "1226",
    "name": "Franche-Comte",
    "country_id": "75"
  }, {
    "id": "1227",
    "name": "Gard",
    "country_id": "75"
  }, {
    "id": "1228",
    "name": "Gers",
    "country_id": "75"
  }, {
    "id": "1229",
    "name": "Gironde",
    "country_id": "75"
  }, {
    "id": "1230",
    "name": "Haut-Rhin",
    "country_id": "75"
  }, {
    "id": "1231",
    "name": "Haute-Corse",
    "country_id": "75"
  }, {
    "id": "1232",
    "name": "Haute-Garonne",
    "country_id": "75"
  }, {
    "id": "1233",
    "name": "Haute-Loire",
    "country_id": "75"
  }, {
    "id": "1234",
    "name": "Haute-Marne",
    "country_id": "75"
  }, {
    "id": "1235",
    "name": "Haute-Saone",
    "country_id": "75"
  }, {
    "id": "1236",
    "name": "Haute-Savoie",
    "country_id": "75"
  }, {
    "id": "1237",
    "name": "Haute-Vienne",
    "country_id": "75"
  }, {
    "id": "1238",
    "name": "Hautes-Alpes",
    "country_id": "75"
  }, {
    "id": "1239",
    "name": "Hautes-Pyrenees",
    "country_id": "75"
  }, {
    "id": "1240",
    "name": "Hauts-de-Seine",
    "country_id": "75"
  }, {
    "id": "1241",
    "name": "Herault",
    "country_id": "75"
  }, {
    "id": "1242",
    "name": "Ile-de-France",
    "country_id": "75"
  }, {
    "id": "1243",
    "name": "Ille-et-Vilaine",
    "country_id": "75"
  }, {
    "id": "1244",
    "name": "Indre",
    "country_id": "75"
  }, {
    "id": "1245",
    "name": "Indre-et-Loire",
    "country_id": "75"
  }, {
    "id": "1246",
    "name": "Isere",
    "country_id": "75"
  }, {
    "id": "1247",
    "name": "Jura",
    "country_id": "75"
  }, {
    "id": "1248",
    "name": "Klagenfurt",
    "country_id": "75"
  }, {
    "id": "1249",
    "name": "Landes",
    "country_id": "75"
  }, {
    "id": "1250",
    "name": "Languedoc-Roussillon",
    "country_id": "75"
  }, {
    "id": "1251",
    "name": "Larcay",
    "country_id": "75"
  }, {
    "id": "1252",
    "name": "Le Castellet",
    "country_id": "75"
  }, {
    "id": "1253",
    "name": "Le Creusot",
    "country_id": "75"
  }, {
    "id": "1254",
    "name": "Limousin",
    "country_id": "75"
  }, {
    "id": "1255",
    "name": "Loir-et-Cher",
    "country_id": "75"
  }, {
    "id": "1256",
    "name": "Loire",
    "country_id": "75"
  }, {
    "id": "1257",
    "name": "Loire-Atlantique",
    "country_id": "75"
  }, {
    "id": "1258",
    "name": "Loiret",
    "country_id": "75"
  }, {
    "id": "1259",
    "name": "Lorraine",
    "country_id": "75"
  }, {
    "id": "1260",
    "name": "Lot",
    "country_id": "75"
  }, {
    "id": "1261",
    "name": "Lot-et-Garonne",
    "country_id": "75"
  }, {
    "id": "1262",
    "name": "Lower Normandy",
    "country_id": "75"
  }, {
    "id": "1263",
    "name": "Lozere",
    "country_id": "75"
  }, {
    "id": "1264",
    "name": "Maine-et-Loire",
    "country_id": "75"
  }, {
    "id": "1265",
    "name": "Manche",
    "country_id": "75"
  }, {
    "id": "1266",
    "name": "Marne",
    "country_id": "75"
  }, {
    "id": "1267",
    "name": "Mayenne",
    "country_id": "75"
  }, {
    "id": "1268",
    "name": "Meurthe-et-Moselle",
    "country_id": "75"
  }, {
    "id": "1269",
    "name": "Meuse",
    "country_id": "75"
  }, {
    "id": "1270",
    "name": "Midi-Pyrenees",
    "country_id": "75"
  }, {
    "id": "1271",
    "name": "Morbihan",
    "country_id": "75"
  }, {
    "id": "1272",
    "name": "Moselle",
    "country_id": "75"
  }, {
    "id": "1273",
    "name": "Nievre",
    "country_id": "75"
  }, {
    "id": "1274",
    "name": "Nord",
    "country_id": "75"
  }, {
    "id": "1275",
    "name": "Nord-Pas-de-Calais",
    "country_id": "75"
  }, {
    "id": "1276",
    "name": "Oise",
    "country_id": "75"
  }, {
    "id": "1277",
    "name": "Orne",
    "country_id": "75"
  }, {
    "id": "1278",
    "name": "Paris",
    "country_id": "75"
  }, {
    "id": "1279",
    "name": "Pas-de-Calais",
    "country_id": "75"
  }, {
    "id": "1280",
    "name": "Pays de la Loire",
    "country_id": "75"
  }, {
    "id": "1281",
    "name": "Pays-de-la-Loire",
    "country_id": "75"
  }, {
    "id": "1282",
    "name": "Picardy",
    "country_id": "75"
  }, {
    "id": "1283",
    "name": "Puy-de-Dome",
    "country_id": "75"
  }, {
    "id": "1284",
    "name": "Pyrenees-Atlantiques",
    "country_id": "75"
  }, {
    "id": "1285",
    "name": "Pyrenees-Orientales",
    "country_id": "75"
  }, {
    "id": "1286",
    "name": "Quelmes",
    "country_id": "75"
  }, {
    "id": "1287",
    "name": "Rhone",
    "country_id": "75"
  }, {
    "id": "1288",
    "name": "Rhone-Alpes",
    "country_id": "75"
  }, {
    "id": "1289",
    "name": "Saint Ouen",
    "country_id": "75"
  }, {
    "id": "1290",
    "name": "Saint Viatre",
    "country_id": "75"
  }, {
    "id": "1291",
    "name": "Saone-et-Loire",
    "country_id": "75"
  }, {
    "id": "1292",
    "name": "Sarthe",
    "country_id": "75"
  }, {
    "id": "1293",
    "name": "Savoie",
    "country_id": "75"
  }, {
    "id": "1294",
    "name": "Seine-Maritime",
    "country_id": "75"
  }, {
    "id": "1295",
    "name": "Seine-Saint-Denis",
    "country_id": "75"
  }, {
    "id": "1296",
    "name": "Seine-et-Marne",
    "country_id": "75"
  }, {
    "id": "1297",
    "name": "Somme",
    "country_id": "75"
  }, {
    "id": "1298",
    "name": "Sophia Antipolis",
    "country_id": "75"
  }, {
    "id": "1299",
    "name": "Souvans",
    "country_id": "75"
  }, {
    "id": "1300",
    "name": "Tarn",
    "country_id": "75"
  }, {
    "id": "1301",
    "name": "Tarn-et-Garonne",
    "country_id": "75"
  }, {
    "id": "1302",
    "name": "Territoire de Belfort",
    "country_id": "75"
  }, {
    "id": "1303",
    "name": "Treignac",
    "country_id": "75"
  }, {
    "id": "1304",
    "name": "Upper Normandy",
    "country_id": "75"
  }, {
    "id": "1305",
    "name": "Val-d'Oise",
    "country_id": "75"
  }, {
    "id": "1306",
    "name": "Val-de-Marne",
    "country_id": "75"
  }, {
    "id": "1307",
    "name": "Var",
    "country_id": "75"
  }, {
    "id": "1308",
    "name": "Vaucluse",
    "country_id": "75"
  }, {
    "id": "1309",
    "name": "Vellise",
    "country_id": "75"
  }, {
    "id": "1310",
    "name": "Vendee",
    "country_id": "75"
  }, {
    "id": "1311",
    "name": "Vienne",
    "country_id": "75"
  }, {
    "id": "1312",
    "name": "Vosges",
    "country_id": "75"
  }, {
    "id": "1313",
    "name": "Yonne",
    "country_id": "75"
  }, {
    "id": "1314",
    "name": "Yvelines",
    "country_id": "75"
  }, {
    "id": "1315",
    "name": "Cayenne",
    "country_id": "76"
  }, {
    "id": "1316",
    "name": "Saint-Laurent-du-Maroni",
    "country_id": "76"
  }, {
    "id": "1317",
    "name": "Iles du Vent",
    "country_id": "77"
  }, {
    "id": "1318",
    "name": "Iles sous le Vent",
    "country_id": "77"
  }, {
    "id": "1319",
    "name": "Marquesas",
    "country_id": "77"
  }, {
    "id": "1320",
    "name": "Tuamotu",
    "country_id": "77"
  }, {
    "id": "1321",
    "name": "Tubuai",
    "country_id": "77"
  }, {
    "id": "1322",
    "name": "Amsterdam",
    "country_id": "78"
  }, {
    "id": "1323",
    "name": "Crozet Islands",
    "country_id": "78"
  }, {
    "id": "1324",
    "name": "Kerguelen",
    "country_id": "78"
  }, {
    "id": "1325",
    "name": "Estuaire",
    "country_id": "79"
  }, {
    "id": "1326",
    "name": "Haut-Ogooue",
    "country_id": "79"
  }, {
    "id": "1327",
    "name": "Moyen-Ogooue",
    "country_id": "79"
  }, {
    "id": "1328",
    "name": "Ngounie",
    "country_id": "79"
  }, {
    "id": "1329",
    "name": "Nyanga",
    "country_id": "79"
  }, {
    "id": "1330",
    "name": "Ogooue-Ivindo",
    "country_id": "79"
  }, {
    "id": "1331",
    "name": "Ogooue-Lolo",
    "country_id": "79"
  }, {
    "id": "1332",
    "name": "Ogooue-Maritime",
    "country_id": "79"
  }, {
    "id": "1333",
    "name": "Woleu-Ntem",
    "country_id": "79"
  }, {
    "id": "1334",
    "name": "Banjul",
    "country_id": "80"
  }, {
    "id": "1335",
    "name": "Basse",
    "country_id": "80"
  }, {
    "id": "1336",
    "name": "Brikama",
    "country_id": "80"
  }, {
    "id": "1337",
    "name": "Janjanbureh",
    "country_id": "80"
  }, {
    "id": "1338",
    "name": "Kanifing",
    "country_id": "80"
  }, {
    "id": "1339",
    "name": "Kerewan",
    "country_id": "80"
  }, {
    "id": "1340",
    "name": "Kuntaur",
    "country_id": "80"
  }, {
    "id": "1341",
    "name": "Mansakonko",
    "country_id": "80"
  }, {
    "id": "1342",
    "name": "Abhasia",
    "country_id": "81"
  }, {
    "id": "1343",
    "name": "Ajaria",
    "country_id": "81"
  }, {
    "id": "1344",
    "name": "Guria",
    "country_id": "81"
  }, {
    "id": "1345",
    "name": "Imereti",
    "country_id": "81"
  }, {
    "id": "1346",
    "name": "Kaheti",
    "country_id": "81"
  }, {
    "id": "1347",
    "name": "Kvemo Kartli",
    "country_id": "81"
  }, {
    "id": "1348",
    "name": "Mcheta-Mtianeti",
    "country_id": "81"
  }, {
    "id": "1349",
    "name": "Racha",
    "country_id": "81"
  }, {
    "id": "1350",
    "name": "Samagrelo-Zemo Svaneti",
    "country_id": "81"
  }, {
    "id": "1351",
    "name": "Samche-Zhavaheti",
    "country_id": "81"
  }, {
    "id": "1352",
    "name": "Shida Kartli",
    "country_id": "81"
  }, {
    "id": "1353",
    "name": "Tbilisi",
    "country_id": "81"
  }, {
    "id": "1354",
    "name": "Auvergne",
    "country_id": "82"
  }, {
    "id": "1355",
    "name": "Baden-Wurttemberg",
    "country_id": "82"
  }, {
    "id": "1356",
    "name": "Bavaria",
    "country_id": "82"
  }, {
    "id": "1357",
    "name": "Bayern",
    "country_id": "82"
  }, {
    "id": "1358",
    "name": "Beilstein Wurtt",
    "country_id": "82"
  }, {
    "id": "1359",
    "name": "Berlin",
    "country_id": "82"
  }, {
    "id": "1360",
    "name": "Brandenburg",
    "country_id": "82"
  }, {
    "id": "1361",
    "name": "Bremen",
    "country_id": "82"
  }, {
    "id": "1362",
    "name": "Dreisbach",
    "country_id": "82"
  }, {
    "id": "1363",
    "name": "Freistaat Bayern",
    "country_id": "82"
  }, {
    "id": "1364",
    "name": "Hamburg",
    "country_id": "82"
  }, {
    "id": "1365",
    "name": "Hannover",
    "country_id": "82"
  }, {
    "id": "1366",
    "name": "Heroldstatt",
    "country_id": "82"
  }, {
    "id": "1367",
    "name": "Hessen",
    "country_id": "82"
  }, {
    "id": "1368",
    "name": "Kortenberg",
    "country_id": "82"
  }, {
    "id": "1369",
    "name": "Laasdorf",
    "country_id": "82"
  }, {
    "id": "1370",
    "name": "Land Baden-Wurttemberg",
    "country_id": "82"
  }, {
    "id": "1371",
    "name": "Land Bayern",
    "country_id": "82"
  }, {
    "id": "1372",
    "name": "Land Brandenburg",
    "country_id": "82"
  }, {
    "id": "1373",
    "name": "Land Hessen",
    "country_id": "82"
  }, {
    "id": "1374",
    "name": "Land Mecklenburg-Vorpommern",
    "country_id": "82"
  }, {
    "id": "1375",
    "name": "Land Nordrhein-Westfalen",
    "country_id": "82"
  }, {
    "id": "1376",
    "name": "Land Rheinland-Pfalz",
    "country_id": "82"
  }, {
    "id": "1377",
    "name": "Land Sachsen",
    "country_id": "82"
  }, {
    "id": "1378",
    "name": "Land Sachsen-Anhalt",
    "country_id": "82"
  }, {
    "id": "1379",
    "name": "Land Thuringen",
    "country_id": "82"
  }, {
    "id": "1380",
    "name": "Lower Saxony",
    "country_id": "82"
  }, {
    "id": "1381",
    "name": "Mecklenburg-Vorpommern",
    "country_id": "82"
  }, {
    "id": "1382",
    "name": "Mulfingen",
    "country_id": "82"
  }, {
    "id": "1383",
    "name": "Munich",
    "country_id": "82"
  }, {
    "id": "1384",
    "name": "Neubeuern",
    "country_id": "82"
  }, {
    "id": "1385",
    "name": "Niedersachsen",
    "country_id": "82"
  }, {
    "id": "1386",
    "name": "Noord-Holland",
    "country_id": "82"
  }, {
    "id": "1387",
    "name": "Nordrhein-Westfalen",
    "country_id": "82"
  }, {
    "id": "1388",
    "name": "North Rhine-Westphalia",
    "country_id": "82"
  }, {
    "id": "1389",
    "name": "Osterode",
    "country_id": "82"
  }, {
    "id": "1390",
    "name": "Rheinland-Pfalz",
    "country_id": "82"
  }, {
    "id": "1391",
    "name": "Rhineland-Palatinate",
    "country_id": "82"
  }, {
    "id": "1392",
    "name": "Saarland",
    "country_id": "82"
  }, {
    "id": "1393",
    "name": "Sachsen",
    "country_id": "82"
  }, {
    "id": "1394",
    "name": "Sachsen-Anhalt",
    "country_id": "82"
  }, {
    "id": "1395",
    "name": "Saxony",
    "country_id": "82"
  }, {
    "id": "1396",
    "name": "Schleswig-Holstein",
    "country_id": "82"
  }, {
    "id": "1397",
    "name": "Thuringia",
    "country_id": "82"
  }, {
    "id": "1398",
    "name": "Webling",
    "country_id": "82"
  }, {
    "id": "1399",
    "name": "Weinstrabe",
    "country_id": "82"
  }, {
    "id": "1400",
    "name": "schlobborn",
    "country_id": "82"
  }, {
    "id": "1401",
    "name": "Ashanti",
    "country_id": "83"
  }, {
    "id": "1402",
    "name": "Brong-Ahafo",
    "country_id": "83"
  }, {
    "id": "1403",
    "name": "Central",
    "country_id": "83"
  }, {
    "id": "1404",
    "name": "Eastern",
    "country_id": "83"
  }, {
    "id": "1405",
    "name": "Greater Accra",
    "country_id": "83"
  }, {
    "id": "1406",
    "name": "Northern",
    "country_id": "83"
  }, {
    "id": "1407",
    "name": "Upper East",
    "country_id": "83"
  }, {
    "id": "1408",
    "name": "Upper West",
    "country_id": "83"
  }, {
    "id": "1409",
    "name": "Volta",
    "country_id": "83"
  }, {
    "id": "1410",
    "name": "Western",
    "country_id": "83"
  }, {
    "id": "1411",
    "name": "Gibraltar",
    "country_id": "84"
  }, {
    "id": "1412",
    "name": "Acharnes",
    "country_id": "85"
  }, {
    "id": "1413",
    "name": "Ahaia",
    "country_id": "85"
  }, {
    "id": "1414",
    "name": "Aitolia kai Akarnania",
    "country_id": "85"
  }, {
    "id": "1415",
    "name": "Argolis",
    "country_id": "85"
  }, {
    "id": "1416",
    "name": "Arkadia",
    "country_id": "85"
  }, {
    "id": "1417",
    "name": "Arta",
    "country_id": "85"
  }, {
    "id": "1418",
    "name": "Attica",
    "country_id": "85"
  }, {
    "id": "1419",
    "name": "Attiki",
    "country_id": "85"
  }, {
    "id": "1420",
    "name": "Ayion Oros",
    "country_id": "85"
  }, {
    "id": "1421",
    "name": "Crete",
    "country_id": "85"
  }, {
    "id": "1422",
    "name": "Dodekanisos",
    "country_id": "85"
  }, {
    "id": "1423",
    "name": "Drama",
    "country_id": "85"
  }, {
    "id": "1424",
    "name": "Evia",
    "country_id": "85"
  }, {
    "id": "1425",
    "name": "Evritania",
    "country_id": "85"
  }, {
    "id": "1426",
    "name": "Evros",
    "country_id": "85"
  }, {
    "id": "1427",
    "name": "Evvoia",
    "country_id": "85"
  }, {
    "id": "1428",
    "name": "Florina",
    "country_id": "85"
  }, {
    "id": "1429",
    "name": "Fokis",
    "country_id": "85"
  }, {
    "id": "1430",
    "name": "Fthiotis",
    "country_id": "85"
  }, {
    "id": "1431",
    "name": "Grevena",
    "country_id": "85"
  }, {
    "id": "1432",
    "name": "Halandri",
    "country_id": "85"
  }, {
    "id": "1433",
    "name": "Halkidiki",
    "country_id": "85"
  }, {
    "id": "1434",
    "name": "Hania",
    "country_id": "85"
  }, {
    "id": "1435",
    "name": "Heraklion",
    "country_id": "85"
  }, {
    "id": "1436",
    "name": "Hios",
    "country_id": "85"
  }, {
    "id": "1437",
    "name": "Ilia",
    "country_id": "85"
  }, {
    "id": "1438",
    "name": "Imathia",
    "country_id": "85"
  }, {
    "id": "1439",
    "name": "Ioannina",
    "country_id": "85"
  }, {
    "id": "1440",
    "name": "Iraklion",
    "country_id": "85"
  }, {
    "id": "1441",
    "name": "Karditsa",
    "country_id": "85"
  }, {
    "id": "1442",
    "name": "Kastoria",
    "country_id": "85"
  }, {
    "id": "1443",
    "name": "Kavala",
    "country_id": "85"
  }, {
    "id": "1444",
    "name": "Kefallinia",
    "country_id": "85"
  }, {
    "id": "1445",
    "name": "Kerkira",
    "country_id": "85"
  }, {
    "id": "1446",
    "name": "Kiklades",
    "country_id": "85"
  }, {
    "id": "1447",
    "name": "Kilkis",
    "country_id": "85"
  }, {
    "id": "1448",
    "name": "Korinthia",
    "country_id": "85"
  }, {
    "id": "1449",
    "name": "Kozani",
    "country_id": "85"
  }, {
    "id": "1450",
    "name": "Lakonia",
    "country_id": "85"
  }, {
    "id": "1451",
    "name": "Larisa",
    "country_id": "85"
  }, {
    "id": "1452",
    "name": "Lasithi",
    "country_id": "85"
  }, {
    "id": "1453",
    "name": "Lesvos",
    "country_id": "85"
  }, {
    "id": "1454",
    "name": "Levkas",
    "country_id": "85"
  }, {
    "id": "1455",
    "name": "Magnisia",
    "country_id": "85"
  }, {
    "id": "1456",
    "name": "Messinia",
    "country_id": "85"
  }, {
    "id": "1457",
    "name": "Nomos Attikis",
    "country_id": "85"
  }, {
    "id": "1458",
    "name": "Nomos Zakynthou",
    "country_id": "85"
  }, {
    "id": "1459",
    "name": "Pella",
    "country_id": "85"
  }, {
    "id": "1460",
    "name": "Pieria",
    "country_id": "85"
  }, {
    "id": "1461",
    "name": "Piraios",
    "country_id": "85"
  }, {
    "id": "1462",
    "name": "Preveza",
    "country_id": "85"
  }, {
    "id": "1463",
    "name": "Rethimni",
    "country_id": "85"
  }, {
    "id": "1464",
    "name": "Rodopi",
    "country_id": "85"
  }, {
    "id": "1465",
    "name": "Samos",
    "country_id": "85"
  }, {
    "id": "1466",
    "name": "Serrai",
    "country_id": "85"
  }, {
    "id": "1467",
    "name": "Thesprotia",
    "country_id": "85"
  }, {
    "id": "1468",
    "name": "Thessaloniki",
    "country_id": "85"
  }, {
    "id": "1469",
    "name": "Trikala",
    "country_id": "85"
  }, {
    "id": "1470",
    "name": "Voiotia",
    "country_id": "85"
  }, {
    "id": "1471",
    "name": "West Greece",
    "country_id": "85"
  }, {
    "id": "1472",
    "name": "Xanthi",
    "country_id": "85"
  }, {
    "id": "1473",
    "name": "Zakinthos",
    "country_id": "85"
  }, {
    "id": "1474",
    "name": "Aasiaat",
    "country_id": "86"
  }, {
    "id": "1475",
    "name": "Ammassalik",
    "country_id": "86"
  }, {
    "id": "1476",
    "name": "Illoqqortoormiut",
    "country_id": "86"
  }, {
    "id": "1477",
    "name": "Ilulissat",
    "country_id": "86"
  }, {
    "id": "1478",
    "name": "Ivittuut",
    "country_id": "86"
  }, {
    "id": "1479",
    "name": "Kangaatsiaq",
    "country_id": "86"
  }, {
    "id": "1480",
    "name": "Maniitsoq",
    "country_id": "86"
  }, {
    "id": "1481",
    "name": "Nanortalik",
    "country_id": "86"
  }, {
    "id": "1482",
    "name": "Narsaq",
    "country_id": "86"
  }, {
    "id": "1483",
    "name": "Nuuk",
    "country_id": "86"
  }, {
    "id": "1484",
    "name": "Paamiut",
    "country_id": "86"
  }, {
    "id": "1485",
    "name": "Qaanaaq",
    "country_id": "86"
  }, {
    "id": "1486",
    "name": "Qaqortoq",
    "country_id": "86"
  }, {
    "id": "1487",
    "name": "Qasigiannguit",
    "country_id": "86"
  }, {
    "id": "1488",
    "name": "Qeqertarsuaq",
    "country_id": "86"
  }, {
    "id": "1489",
    "name": "Sisimiut",
    "country_id": "86"
  }, {
    "id": "1490",
    "name": "Udenfor kommunal inddeling",
    "country_id": "86"
  }, {
    "id": "1491",
    "name": "Upernavik",
    "country_id": "86"
  }, {
    "id": "1492",
    "name": "Uummannaq",
    "country_id": "86"
  }, {
    "id": "1493",
    "name": "Carriacou-Petite Martinique",
    "country_id": "87"
  }, {
    "id": "1494",
    "name": "Saint Andrew",
    "country_id": "87"
  }, {
    "id": "1495",
    "name": "Saint Davids",
    "country_id": "87"
  }, {
    "id": "1496",
    "name": "Saint George's",
    "country_id": "87"
  }, {
    "id": "1497",
    "name": "Saint John",
    "country_id": "87"
  }, {
    "id": "1498",
    "name": "Saint Mark",
    "country_id": "87"
  }, {
    "id": "1499",
    "name": "Saint Patrick",
    "country_id": "87"
  }, {
    "id": "1500",
    "name": "Basse-Terre",
    "country_id": "88"
  }, {
    "id": "1501",
    "name": "Grande-Terre",
    "country_id": "88"
  }, {
    "id": "1502",
    "name": "Iles des Saintes",
    "country_id": "88"
  }, {
    "id": "1503",
    "name": "La Desirade",
    "country_id": "88"
  }, {
    "id": "1504",
    "name": "Marie-Galante",
    "country_id": "88"
  }, {
    "id": "1505",
    "name": "Saint Barthelemy",
    "country_id": "88"
  }, {
    "id": "1506",
    "name": "Saint Martin",
    "country_id": "88"
  }, {
    "id": "1507",
    "name": "Agana Heights",
    "country_id": "89"
  }, {
    "id": "1508",
    "name": "Agat",
    "country_id": "89"
  }, {
    "id": "1509",
    "name": "Barrigada",
    "country_id": "89"
  }, {
    "id": "1510",
    "name": "Chalan-Pago-Ordot",
    "country_id": "89"
  }, {
    "id": "1511",
    "name": "Dededo",
    "country_id": "89"
  }, {
    "id": "1512",
    "name": "Hagatna",
    "country_id": "89"
  }, {
    "id": "1513",
    "name": "Inarajan",
    "country_id": "89"
  }, {
    "id": "1514",
    "name": "Mangilao",
    "country_id": "89"
  }, {
    "id": "1515",
    "name": "Merizo",
    "country_id": "89"
  }, {
    "id": "1516",
    "name": "Mongmong-Toto-Maite",
    "country_id": "89"
  }, {
    "id": "1517",
    "name": "Santa Rita",
    "country_id": "89"
  }, {
    "id": "1518",
    "name": "Sinajana",
    "country_id": "89"
  }, {
    "id": "1519",
    "name": "Talofofo",
    "country_id": "89"
  }, {
    "id": "1520",
    "name": "Tamuning",
    "country_id": "89"
  }, {
    "id": "1521",
    "name": "Yigo",
    "country_id": "89"
  }, {
    "id": "1522",
    "name": "Yona",
    "country_id": "89"
  }, {
    "id": "1523",
    "name": "Alta Verapaz",
    "country_id": "90"
  }, {
    "id": "1524",
    "name": "Baja Verapaz",
    "country_id": "90"
  }, {
    "id": "1525",
    "name": "Chimaltenango",
    "country_id": "90"
  }, {
    "id": "1526",
    "name": "Chiquimula",
    "country_id": "90"
  }, {
    "id": "1527",
    "name": "El Progreso",
    "country_id": "90"
  }, {
    "id": "1528",
    "name": "Escuintla",
    "country_id": "90"
  }, {
    "id": "1529",
    "name": "Guatemala",
    "country_id": "90"
  }, {
    "id": "1530",
    "name": "Huehuetenango",
    "country_id": "90"
  }, {
    "id": "1531",
    "name": "Izabal",
    "country_id": "90"
  }, {
    "id": "1532",
    "name": "Jalapa",
    "country_id": "90"
  }, {
    "id": "1533",
    "name": "Jutiapa",
    "country_id": "90"
  }, {
    "id": "1534",
    "name": "Peten",
    "country_id": "90"
  }, {
    "id": "1535",
    "name": "Quezaltenango",
    "country_id": "90"
  }, {
    "id": "1536",
    "name": "Quiche",
    "country_id": "90"
  }, {
    "id": "1537",
    "name": "Retalhuleu",
    "country_id": "90"
  }, {
    "id": "1538",
    "name": "Sacatepequez",
    "country_id": "90"
  }, {
    "id": "1539",
    "name": "San Marcos",
    "country_id": "90"
  }, {
    "id": "1540",
    "name": "Santa Rosa",
    "country_id": "90"
  }, {
    "id": "1541",
    "name": "Solola",
    "country_id": "90"
  }, {
    "id": "1542",
    "name": "Suchitepequez",
    "country_id": "90"
  }, {
    "id": "1543",
    "name": "Totonicapan",
    "country_id": "90"
  }, {
    "id": "1544",
    "name": "Zacapa",
    "country_id": "90"
  }, {
    "id": "1545",
    "name": "Alderney",
    "country_id": "91"
  }, {
    "id": "1546",
    "name": "Castel",
    "country_id": "91"
  }, {
    "id": "1547",
    "name": "Forest",
    "country_id": "91"
  }, {
    "id": "1548",
    "name": "Saint Andrew",
    "country_id": "91"
  }, {
    "id": "1549",
    "name": "Saint Martin",
    "country_id": "91"
  }, {
    "id": "1550",
    "name": "Saint Peter Port",
    "country_id": "91"
  }, {
    "id": "1551",
    "name": "Saint Pierre du Bois",
    "country_id": "91"
  }, {
    "id": "1552",
    "name": "Saint Sampson",
    "country_id": "91"
  }, {
    "id": "1553",
    "name": "Saint Saviour",
    "country_id": "91"
  }, {
    "id": "1554",
    "name": "Sark",
    "country_id": "91"
  }, {
    "id": "1555",
    "name": "Torteval",
    "country_id": "91"
  }, {
    "id": "1556",
    "name": "Vale",
    "country_id": "91"
  }, {
    "id": "1557",
    "name": "Beyla",
    "country_id": "92"
  }, {
    "id": "1558",
    "name": "Boffa",
    "country_id": "92"
  }, {
    "id": "1559",
    "name": "Boke",
    "country_id": "92"
  }, {
    "id": "1560",
    "name": "Conakry",
    "country_id": "92"
  }, {
    "id": "1561",
    "name": "Coyah",
    "country_id": "92"
  }, {
    "id": "1562",
    "name": "Dabola",
    "country_id": "92"
  }, {
    "id": "1563",
    "name": "Dalaba",
    "country_id": "92"
  }, {
    "id": "1564",
    "name": "Dinguiraye",
    "country_id": "92"
  }, {
    "id": "1565",
    "name": "Faranah",
    "country_id": "92"
  }, {
    "id": "1566",
    "name": "Forecariah",
    "country_id": "92"
  }, {
    "id": "1567",
    "name": "Fria",
    "country_id": "92"
  }, {
    "id": "1568",
    "name": "Gaoual",
    "country_id": "92"
  }, {
    "id": "1569",
    "name": "Gueckedou",
    "country_id": "92"
  }, {
    "id": "1570",
    "name": "Kankan",
    "country_id": "92"
  }, {
    "id": "1571",
    "name": "Kerouane",
    "country_id": "92"
  }, {
    "id": "1572",
    "name": "Kindia",
    "country_id": "92"
  }, {
    "id": "1573",
    "name": "Kissidougou",
    "country_id": "92"
  }, {
    "id": "1574",
    "name": "Koubia",
    "country_id": "92"
  }, {
    "id": "1575",
    "name": "Koundara",
    "country_id": "92"
  }, {
    "id": "1576",
    "name": "Kouroussa",
    "country_id": "92"
  }, {
    "id": "1577",
    "name": "Labe",
    "country_id": "92"
  }, {
    "id": "1578",
    "name": "Lola",
    "country_id": "92"
  }, {
    "id": "1579",
    "name": "Macenta",
    "country_id": "92"
  }, {
    "id": "1580",
    "name": "Mali",
    "country_id": "92"
  }, {
    "id": "1581",
    "name": "Mamou",
    "country_id": "92"
  }, {
    "id": "1582",
    "name": "Mandiana",
    "country_id": "92"
  }, {
    "id": "1583",
    "name": "Nzerekore",
    "country_id": "92"
  }, {
    "id": "1584",
    "name": "Pita",
    "country_id": "92"
  }, {
    "id": "1585",
    "name": "Siguiri",
    "country_id": "92"
  }, {
    "id": "1586",
    "name": "Telimele",
    "country_id": "92"
  }, {
    "id": "1587",
    "name": "Tougue",
    "country_id": "92"
  }, {
    "id": "1588",
    "name": "Yomou",
    "country_id": "92"
  }, {
    "id": "1589",
    "name": "Bafata",
    "country_id": "93"
  }, {
    "id": "1590",
    "name": "Bissau",
    "country_id": "93"
  }, {
    "id": "1591",
    "name": "Bolama",
    "country_id": "93"
  }, {
    "id": "1592",
    "name": "Cacheu",
    "country_id": "93"
  }, {
    "id": "1593",
    "name": "Gabu",
    "country_id": "93"
  }, {
    "id": "1594",
    "name": "Oio",
    "country_id": "93"
  }, {
    "id": "1595",
    "name": "Quinara",
    "country_id": "93"
  }, {
    "id": "1596",
    "name": "Tombali",
    "country_id": "93"
  }, {
    "id": "1597",
    "name": "Barima-Waini",
    "country_id": "94"
  }, {
    "id": "1598",
    "name": "Cuyuni-Mazaruni",
    "country_id": "94"
  }, {
    "id": "1599",
    "name": "Demerara-Mahaica",
    "country_id": "94"
  }, {
    "id": "1600",
    "name": "East Berbice-Corentyne",
    "country_id": "94"
  }, {
    "id": "1601",
    "name": "Essequibo Islands-West Demerar",
    "country_id": "94"
  }, {
    "id": "1602",
    "name": "Mahaica-Berbice",
    "country_id": "94"
  }, {
    "id": "1603",
    "name": "Pomeroon-Supenaam",
    "country_id": "94"
  }, {
    "id": "1604",
    "name": "Potaro-Siparuni",
    "country_id": "94"
  }, {
    "id": "1605",
    "name": "Upper Demerara-Berbice",
    "country_id": "94"
  }, {
    "id": "1606",
    "name": "Upper Takutu-Upper Essequibo",
    "country_id": "94"
  }, {
    "id": "1607",
    "name": "Artibonite",
    "country_id": "95"
  }, {
    "id": "1608",
    "name": "Centre",
    "country_id": "95"
  }, {
    "id": "1609",
    "name": "Grand'Anse",
    "country_id": "95"
  }, {
    "id": "1610",
    "name": "Nord",
    "country_id": "95"
  }, {
    "id": "1611",
    "name": "Nord-Est",
    "country_id": "95"
  }, {
    "id": "1612",
    "name": "Nord-Ouest",
    "country_id": "95"
  }, {
    "id": "1613",
    "name": "Ouest",
    "country_id": "95"
  }, {
    "id": "1614",
    "name": "Sud",
    "country_id": "95"
  }, {
    "id": "1615",
    "name": "Sud-Est",
    "country_id": "95"
  }, {
    "id": "1616",
    "name": "Heard and McDonald Islands",
    "country_id": "96"
  }, {
    "id": "1617",
    "name": "Atlantida",
    "country_id": "97"
  }, {
    "id": "1618",
    "name": "Choluteca",
    "country_id": "97"
  }, {
    "id": "1619",
    "name": "Colon",
    "country_id": "97"
  }, {
    "id": "1620",
    "name": "Comayagua",
    "country_id": "97"
  }, {
    "id": "1621",
    "name": "Copan",
    "country_id": "97"
  }, {
    "id": "1622",
    "name": "Cortes",
    "country_id": "97"
  }, {
    "id": "1623",
    "name": "Distrito Central",
    "country_id": "97"
  }, {
    "id": "1624",
    "name": "El Paraiso",
    "country_id": "97"
  }, {
    "id": "1625",
    "name": "Francisco Morazan",
    "country_id": "97"
  }, {
    "id": "1626",
    "name": "Gracias a Dios",
    "country_id": "97"
  }, {
    "id": "1627",
    "name": "Intibuca",
    "country_id": "97"
  }, {
    "id": "1628",
    "name": "Islas de la Bahia",
    "country_id": "97"
  }, {
    "id": "1629",
    "name": "La Paz",
    "country_id": "97"
  }, {
    "id": "1630",
    "name": "Lempira",
    "country_id": "97"
  }, {
    "id": "1631",
    "name": "Ocotepeque",
    "country_id": "97"
  }, {
    "id": "1632",
    "name": "Olancho",
    "country_id": "97"
  }, {
    "id": "1633",
    "name": "Santa Barbara",
    "country_id": "97"
  }, {
    "id": "1634",
    "name": "Valle",
    "country_id": "97"
  }, {
    "id": "1635",
    "name": "Yoro",
    "country_id": "97"
  }, {
    "id": "1636",
    "name": "Hong Kong",
    "country_id": "98"
  }, {
    "id": "1637",
    "name": "Bacs-Kiskun",
    "country_id": "99"
  }, {
    "id": "1638",
    "name": "Baranya",
    "country_id": "99"
  }, {
    "id": "1639",
    "name": "Bekes",
    "country_id": "99"
  }, {
    "id": "1640",
    "name": "Borsod-Abauj-Zemplen",
    "country_id": "99"
  }, {
    "id": "1641",
    "name": "Budapest",
    "country_id": "99"
  }, {
    "id": "1642",
    "name": "Csongrad",
    "country_id": "99"
  }, {
    "id": "1643",
    "name": "Fejer",
    "country_id": "99"
  }, {
    "id": "1644",
    "name": "Gyor-Moson-Sopron",
    "country_id": "99"
  }, {
    "id": "1645",
    "name": "Hajdu-Bihar",
    "country_id": "99"
  }, {
    "id": "1646",
    "name": "Heves",
    "country_id": "99"
  }, {
    "id": "1647",
    "name": "Jasz-Nagykun-Szolnok",
    "country_id": "99"
  }, {
    "id": "1648",
    "name": "Komarom-Esztergom",
    "country_id": "99"
  }, {
    "id": "1649",
    "name": "Nograd",
    "country_id": "99"
  }, {
    "id": "1650",
    "name": "Pest",
    "country_id": "99"
  }, {
    "id": "1651",
    "name": "Somogy",
    "country_id": "99"
  }, {
    "id": "1652",
    "name": "Szabolcs-Szatmar-Bereg",
    "country_id": "99"
  }, {
    "id": "1653",
    "name": "Tolna",
    "country_id": "99"
  }, {
    "id": "1654",
    "name": "Vas",
    "country_id": "99"
  }, {
    "id": "1655",
    "name": "Veszprem",
    "country_id": "99"
  }, {
    "id": "1656",
    "name": "Zala",
    "country_id": "99"
  }, {
    "id": "1657",
    "name": "Austurland",
    "country_id": "100"
  }, {
    "id": "1658",
    "name": "Gullbringusysla",
    "country_id": "100"
  }, {
    "id": "1659",
    "name": "Hofu borgarsva i",
    "country_id": "100"
  }, {
    "id": "1660",
    "name": "Nor urland eystra",
    "country_id": "100"
  }, {
    "id": "1661",
    "name": "Nor urland vestra",
    "country_id": "100"
  }, {
    "id": "1662",
    "name": "Su urland",
    "country_id": "100"
  }, {
    "id": "1663",
    "name": "Su urnes",
    "country_id": "100"
  }, {
    "id": "1664",
    "name": "Vestfir ir",
    "country_id": "100"
  }, {
    "id": "1665",
    "name": "Vesturland",
    "country_id": "100"
  }, {
    "id": "1666",
    "name": "Aceh",
    "country_id": "102"
  }, {
    "id": "1667",
    "name": "Bali",
    "country_id": "102"
  }, {
    "id": "1668",
    "name": "Bangka-Belitung",
    "country_id": "102"
  }, {
    "id": "1669",
    "name": "Banten",
    "country_id": "102"
  }, {
    "id": "1670",
    "name": "Bengkulu",
    "country_id": "102"
  }, {
    "id": "1671",
    "name": "Gandaria",
    "country_id": "102"
  }, {
    "id": "1672",
    "name": "Gorontalo",
    "country_id": "102"
  }, {
    "id": "1673",
    "name": "Jakarta",
    "country_id": "102"
  }, {
    "id": "1674",
    "name": "Jambi",
    "country_id": "102"
  }, {
    "id": "1675",
    "name": "Jawa Barat",
    "country_id": "102"
  }, {
    "id": "1676",
    "name": "Jawa Tengah",
    "country_id": "102"
  }, {
    "id": "1677",
    "name": "Jawa Timur",
    "country_id": "102"
  }, {
    "id": "1678",
    "name": "Kalimantan Barat",
    "country_id": "102"
  }, {
    "id": "1679",
    "name": "Kalimantan Selatan",
    "country_id": "102"
  }, {
    "id": "1680",
    "name": "Kalimantan Tengah",
    "country_id": "102"
  }, {
    "id": "1681",
    "name": "Kalimantan Timur",
    "country_id": "102"
  }, {
    "id": "1682",
    "name": "Kendal",
    "country_id": "102"
  }, {
    "id": "1683",
    "name": "Lampung",
    "country_id": "102"
  }, {
    "id": "1684",
    "name": "Maluku",
    "country_id": "102"
  }, {
    "id": "1685",
    "name": "Maluku Utara",
    "country_id": "102"
  }, {
    "id": "1686",
    "name": "Nusa Tenggara Barat",
    "country_id": "102"
  }, {
    "id": "1687",
    "name": "Nusa Tenggara Timur",
    "country_id": "102"
  }, {
    "id": "1688",
    "name": "Papua",
    "country_id": "102"
  }, {
    "id": "1689",
    "name": "Riau",
    "country_id": "102"
  }, {
    "id": "1690",
    "name": "Riau Kepulauan",
    "country_id": "102"
  }, {
    "id": "1691",
    "name": "Solo",
    "country_id": "102"
  }, {
    "id": "1692",
    "name": "Sulawesi Selatan",
    "country_id": "102"
  }, {
    "id": "1693",
    "name": "Sulawesi Tengah",
    "country_id": "102"
  }, {
    "id": "1694",
    "name": "Sulawesi Tenggara",
    "country_id": "102"
  }, {
    "id": "1695",
    "name": "Sulawesi Utara",
    "country_id": "102"
  }, {
    "id": "1696",
    "name": "Sumatera Barat",
    "country_id": "102"
  }, {
    "id": "1697",
    "name": "Sumatera Selatan",
    "country_id": "102"
  }, {
    "id": "1698",
    "name": "Sumatera Utara",
    "country_id": "102"
  }, {
    "id": "1699",
    "name": "Yogyakarta",
    "country_id": "102"
  }, {
    "id": "1700",
    "name": "Ardabil",
    "country_id": "103"
  }, {
    "id": "1701",
    "name": "Azarbayjan-e Bakhtari",
    "country_id": "103"
  }, {
    "id": "1702",
    "name": "Azarbayjan-e Khavari",
    "country_id": "103"
  }, {
    "id": "1703",
    "name": "Bushehr",
    "country_id": "103"
  }, {
    "id": "1704",
    "name": "Chahar Mahal-e Bakhtiari",
    "country_id": "103"
  }, {
    "id": "1705",
    "name": "Esfahan",
    "country_id": "103"
  }, {
    "id": "1706",
    "name": "Fars",
    "country_id": "103"
  }, {
    "id": "1707",
    "name": "Gilan",
    "country_id": "103"
  }, {
    "id": "1708",
    "name": "Golestan",
    "country_id": "103"
  }, {
    "id": "1709",
    "name": "Hamadan",
    "country_id": "103"
  }, {
    "id": "1710",
    "name": "Hormozgan",
    "country_id": "103"
  }, {
    "id": "1711",
    "name": "Ilam",
    "country_id": "103"
  }, {
    "id": "1712",
    "name": "Kerman",
    "country_id": "103"
  }, {
    "id": "1713",
    "name": "Kermanshah",
    "country_id": "103"
  }, {
    "id": "1714",
    "name": "Khorasan",
    "country_id": "103"
  }, {
    "id": "1715",
    "name": "Khuzestan",
    "country_id": "103"
  }, {
    "id": "1716",
    "name": "Kohgiluyeh-e Boyerahmad",
    "country_id": "103"
  }, {
    "id": "1717",
    "name": "Kordestan",
    "country_id": "103"
  }, {
    "id": "1718",
    "name": "Lorestan",
    "country_id": "103"
  }, {
    "id": "1719",
    "name": "Markazi",
    "country_id": "103"
  }, {
    "id": "1720",
    "name": "Mazandaran",
    "country_id": "103"
  }, {
    "id": "1721",
    "name": "Ostan-e Esfahan",
    "country_id": "103"
  }, {
    "id": "1722",
    "name": "Qazvin",
    "country_id": "103"
  }, {
    "id": "1723",
    "name": "Qom",
    "country_id": "103"
  }, {
    "id": "1724",
    "name": "Semnan",
    "country_id": "103"
  }, {
    "id": "1725",
    "name": "Sistan-e Baluchestan",
    "country_id": "103"
  }, {
    "id": "1726",
    "name": "Tehran",
    "country_id": "103"
  }, {
    "id": "1727",
    "name": "Yazd",
    "country_id": "103"
  }, {
    "id": "1728",
    "name": "Zanjan",
    "country_id": "103"
  }, {
    "id": "1729",
    "name": "Babil",
    "country_id": "104"
  }, {
    "id": "1730",
    "name": "Baghdad",
    "country_id": "104"
  }, {
    "id": "1731",
    "name": "Dahuk",
    "country_id": "104"
  }, {
    "id": "1732",
    "name": "Dhi Qar",
    "country_id": "104"
  }, {
    "id": "1733",
    "name": "Diyala",
    "country_id": "104"
  }, {
    "id": "1734",
    "name": "Erbil",
    "country_id": "104"
  }, {
    "id": "1735",
    "name": "Irbil",
    "country_id": "104"
  }, {
    "id": "1736",
    "name": "Karbala",
    "country_id": "104"
  }, {
    "id": "1737",
    "name": "Kurdistan",
    "country_id": "104"
  }, {
    "id": "1738",
    "name": "Maysan",
    "country_id": "104"
  }, {
    "id": "1739",
    "name": "Ninawa",
    "country_id": "104"
  }, {
    "id": "1740",
    "name": "Salah-ad-Din",
    "country_id": "104"
  }, {
    "id": "1741",
    "name": "Wasit",
    "country_id": "104"
  }, {
    "id": "1742",
    "name": "al-Anbar",
    "country_id": "104"
  }, {
    "id": "1743",
    "name": "al-Basrah",
    "country_id": "104"
  }, {
    "id": "1744",
    "name": "al-Muthanna",
    "country_id": "104"
  }, {
    "id": "1745",
    "name": "al-Qadisiyah",
    "country_id": "104"
  }, {
    "id": "1746",
    "name": "an-Najaf",
    "country_id": "104"
  }, {
    "id": "1747",
    "name": "as-Sulaymaniyah",
    "country_id": "104"
  }, {
    "id": "1748",
    "name": "at-Ta'mim",
    "country_id": "104"
  }, {
    "id": "1749",
    "name": "Armagh",
    "country_id": "105"
  }, {
    "id": "1750",
    "name": "Carlow",
    "country_id": "105"
  }, {
    "id": "1751",
    "name": "Cavan",
    "country_id": "105"
  }, {
    "id": "1752",
    "name": "Clare",
    "country_id": "105"
  }, {
    "id": "1753",
    "name": "Cork",
    "country_id": "105"
  }, {
    "id": "1754",
    "name": "Donegal",
    "country_id": "105"
  }, {
    "id": "1755",
    "name": "Dublin",
    "country_id": "105"
  }, {
    "id": "1756",
    "name": "Galway",
    "country_id": "105"
  }, {
    "id": "1757",
    "name": "Kerry",
    "country_id": "105"
  }, {
    "id": "1758",
    "name": "Kildare",
    "country_id": "105"
  }, {
    "id": "1759",
    "name": "Kilkenny",
    "country_id": "105"
  }, {
    "id": "1760",
    "name": "Laois",
    "country_id": "105"
  }, {
    "id": "1761",
    "name": "Leinster",
    "country_id": "105"
  }, {
    "id": "1762",
    "name": "Leitrim",
    "country_id": "105"
  }, {
    "id": "1763",
    "name": "Limerick",
    "country_id": "105"
  }, {
    "id": "1764",
    "name": "Loch Garman",
    "country_id": "105"
  }, {
    "id": "1765",
    "name": "Longford",
    "country_id": "105"
  }, {
    "id": "1766",
    "name": "Louth",
    "country_id": "105"
  }, {
    "id": "1767",
    "name": "Mayo",
    "country_id": "105"
  }, {
    "id": "1768",
    "name": "Meath",
    "country_id": "105"
  }, {
    "id": "1769",
    "name": "Monaghan",
    "country_id": "105"
  }, {
    "id": "1770",
    "name": "Offaly",
    "country_id": "105"
  }, {
    "id": "1771",
    "name": "Roscommon",
    "country_id": "105"
  }, {
    "id": "1772",
    "name": "Sligo",
    "country_id": "105"
  }, {
    "id": "1773",
    "name": "Tipperary North Riding",
    "country_id": "105"
  }, {
    "id": "1774",
    "name": "Tipperary South Riding",
    "country_id": "105"
  }, {
    "id": "1775",
    "name": "Ulster",
    "country_id": "105"
  }, {
    "id": "1776",
    "name": "Waterford",
    "country_id": "105"
  }, {
    "id": "1777",
    "name": "Westmeath",
    "country_id": "105"
  }, {
    "id": "1778",
    "name": "Wexford",
    "country_id": "105"
  }, {
    "id": "1779",
    "name": "Wicklow",
    "country_id": "105"
  }, {
    "id": "1780",
    "name": "Beit Hanania",
    "country_id": "106"
  }, {
    "id": "1781",
    "name": "Ben Gurion Airport",
    "country_id": "106"
  }, {
    "id": "1782",
    "name": "Bethlehem",
    "country_id": "106"
  }, {
    "id": "1783",
    "name": "Caesarea",
    "country_id": "106"
  }, {
    "id": "1784",
    "name": "Centre",
    "country_id": "106"
  }, {
    "id": "1785",
    "name": "Gaza",
    "country_id": "106"
  }, {
    "id": "1786",
    "name": "Hadaron",
    "country_id": "106"
  }, {
    "id": "1787",
    "name": "Haifa District",
    "country_id": "106"
  }, {
    "id": "1788",
    "name": "Hamerkaz",
    "country_id": "106"
  }, {
    "id": "1789",
    "name": "Hazafon",
    "country_id": "106"
  }, {
    "id": "1790",
    "name": "Hebron",
    "country_id": "106"
  }, {
    "id": "1791",
    "name": "Jaffa",
    "country_id": "106"
  }, {
    "id": "1792",
    "name": "Jerusalem",
    "country_id": "106"
  }, {
    "id": "1793",
    "name": "Khefa",
    "country_id": "106"
  }, {
    "id": "1794",
    "name": "Kiryat Yam",
    "country_id": "106"
  }, {
    "id": "1795",
    "name": "Lower Galilee",
    "country_id": "106"
  }, {
    "id": "1796",
    "name": "Qalqilya",
    "country_id": "106"
  }, {
    "id": "1797",
    "name": "Talme Elazar",
    "country_id": "106"
  }, {
    "id": "1798",
    "name": "Tel Aviv",
    "country_id": "106"
  }, {
    "id": "1799",
    "name": "Tsafon",
    "country_id": "106"
  }, {
    "id": "1800",
    "name": "Umm El Fahem",
    "country_id": "106"
  }, {
    "id": "1801",
    "name": "Yerushalayim",
    "country_id": "106"
  }, {
    "id": "1802",
    "name": "Abruzzi",
    "country_id": "107"
  }, {
    "id": "1803",
    "name": "Abruzzo",
    "country_id": "107"
  }, {
    "id": "1804",
    "name": "Agrigento",
    "country_id": "107"
  }, {
    "id": "1805",
    "name": "Alessandria",
    "country_id": "107"
  }, {
    "id": "1806",
    "name": "Ancona",
    "country_id": "107"
  }, {
    "id": "1807",
    "name": "Arezzo",
    "country_id": "107"
  }, {
    "id": "1808",
    "name": "Ascoli Piceno",
    "country_id": "107"
  }, {
    "id": "1809",
    "name": "Asti",
    "country_id": "107"
  }, {
    "id": "1810",
    "name": "Avellino",
    "country_id": "107"
  }, {
    "id": "1811",
    "name": "Bari",
    "country_id": "107"
  }, {
    "id": "1812",
    "name": "Basilicata",
    "country_id": "107"
  }, {
    "id": "1813",
    "name": "Belluno",
    "country_id": "107"
  }, {
    "id": "1814",
    "name": "Benevento",
    "country_id": "107"
  }, {
    "id": "1815",
    "name": "Bergamo",
    "country_id": "107"
  }, {
    "id": "1816",
    "name": "Biella",
    "country_id": "107"
  }, {
    "id": "1817",
    "name": "Bologna",
    "country_id": "107"
  }, {
    "id": "1818",
    "name": "Bolzano",
    "country_id": "107"
  }, {
    "id": "1819",
    "name": "Brescia",
    "country_id": "107"
  }, {
    "id": "1820",
    "name": "Brindisi",
    "country_id": "107"
  }, {
    "id": "1821",
    "name": "Calabria",
    "country_id": "107"
  }, {
    "id": "1822",
    "name": "Campania",
    "country_id": "107"
  }, {
    "id": "1823",
    "name": "Cartoceto",
    "country_id": "107"
  }, {
    "id": "1824",
    "name": "Caserta",
    "country_id": "107"
  }, {
    "id": "1825",
    "name": "Catania",
    "country_id": "107"
  }, {
    "id": "1826",
    "name": "Chieti",
    "country_id": "107"
  }, {
    "id": "1827",
    "name": "Como",
    "country_id": "107"
  }, {
    "id": "1828",
    "name": "Cosenza",
    "country_id": "107"
  }, {
    "id": "1829",
    "name": "Cremona",
    "country_id": "107"
  }, {
    "id": "1830",
    "name": "Cuneo",
    "country_id": "107"
  }, {
    "id": "1831",
    "name": "Emilia-Romagna",
    "country_id": "107"
  }, {
    "id": "1832",
    "name": "Ferrara",
    "country_id": "107"
  }, {
    "id": "1833",
    "name": "Firenze",
    "country_id": "107"
  }, {
    "id": "1834",
    "name": "Florence",
    "country_id": "107"
  }, {
    "id": "1835",
    "name": "Forli-Cesena ",
    "country_id": "107"
  }, {
    "id": "1836",
    "name": "Friuli-Venezia Giulia",
    "country_id": "107"
  }, {
    "id": "1837",
    "name": "Frosinone",
    "country_id": "107"
  }, {
    "id": "1838",
    "name": "Genoa",
    "country_id": "107"
  }, {
    "id": "1839",
    "name": "Gorizia",
    "country_id": "107"
  }, {
    "id": "1840",
    "name": "L'Aquila",
    "country_id": "107"
  }, {
    "id": "1841",
    "name": "Lazio",
    "country_id": "107"
  }, {
    "id": "1842",
    "name": "Lecce",
    "country_id": "107"
  }, {
    "id": "1843",
    "name": "Lecco",
    "country_id": "107"
  }, {
    "id": "1845",
    "name": "Liguria",
    "country_id": "107"
  }, {
    "id": "1846",
    "name": "Lodi",
    "country_id": "107"
  }, {
    "id": "1847",
    "name": "Lombardia",
    "country_id": "107"
  }, {
    "id": "1848",
    "name": "Lombardy",
    "country_id": "107"
  }, {
    "id": "1849",
    "name": "Macerata",
    "country_id": "107"
  }, {
    "id": "1850",
    "name": "Mantova",
    "country_id": "107"
  }, {
    "id": "1851",
    "name": "Marche",
    "country_id": "107"
  }, {
    "id": "1852",
    "name": "Messina",
    "country_id": "107"
  }, {
    "id": "1853",
    "name": "Milan",
    "country_id": "107"
  }, {
    "id": "1854",
    "name": "Modena",
    "country_id": "107"
  }, {
    "id": "1855",
    "name": "Molise",
    "country_id": "107"
  }, {
    "id": "1856",
    "name": "Molteno",
    "country_id": "107"
  }, {
    "id": "1857",
    "name": "Montenegro",
    "country_id": "107"
  }, {
    "id": "1858",
    "name": "Monza and Brianza",
    "country_id": "107"
  }, {
    "id": "1859",
    "name": "Naples",
    "country_id": "107"
  }, {
    "id": "1860",
    "name": "Novara",
    "country_id": "107"
  }, {
    "id": "1861",
    "name": "Padova",
    "country_id": "107"
  }, {
    "id": "1862",
    "name": "Parma",
    "country_id": "107"
  }, {
    "id": "1863",
    "name": "Pavia",
    "country_id": "107"
  }, {
    "id": "1864",
    "name": "Perugia",
    "country_id": "107"
  }, {
    "id": "1865",
    "name": "Pesaro-Urbino",
    "country_id": "107"
  }, {
    "id": "1866",
    "name": "Piacenza",
    "country_id": "107"
  }, {
    "id": "1867",
    "name": "Piedmont",
    "country_id": "107"
  }, {
    "id": "1868",
    "name": "Piemonte",
    "country_id": "107"
  }, {
    "id": "1869",
    "name": "Pisa",
    "country_id": "107"
  }, {
    "id": "1870",
    "name": "Pordenone",
    "country_id": "107"
  }, {
    "id": "1871",
    "name": "Potenza",
    "country_id": "107"
  }, {
    "id": "1872",
    "name": "Puglia",
    "country_id": "107"
  }, {
    "id": "1873",
    "name": "Reggio Emilia",
    "country_id": "107"
  }, {
    "id": "1874",
    "name": "Rimini",
    "country_id": "107"
  }, {
    "id": "1875",
    "name": "Roma",
    "country_id": "107"
  }, {
    "id": "1876",
    "name": "Salerno",
    "country_id": "107"
  }, {
    "id": "1877",
    "name": "Sardegna",
    "country_id": "107"
  }, {
    "id": "1878",
    "name": "Sassari",
    "country_id": "107"
  }, {
    "id": "1879",
    "name": "Savona",
    "country_id": "107"
  }, {
    "id": "1880",
    "name": "Sicilia",
    "country_id": "107"
  }, {
    "id": "1881",
    "name": "Siena",
    "country_id": "107"
  }, {
    "id": "1882",
    "name": "Sondrio",
    "country_id": "107"
  }, {
    "id": "1883",
    "name": "South Tyrol",
    "country_id": "107"
  }, {
    "id": "1884",
    "name": "Taranto",
    "country_id": "107"
  }, {
    "id": "1885",
    "name": "Teramo",
    "country_id": "107"
  }, {
    "id": "1886",
    "name": "Torino",
    "country_id": "107"
  }, {
    "id": "1887",
    "name": "Toscana",
    "country_id": "107"
  }, {
    "id": "1888",
    "name": "Trapani",
    "country_id": "107"
  }, {
    "id": "1889",
    "name": "Trentino-Alto Adige",
    "country_id": "107"
  }, {
    "id": "1890",
    "name": "Trento",
    "country_id": "107"
  }, {
    "id": "1891",
    "name": "Treviso",
    "country_id": "107"
  }, {
    "id": "1892",
    "name": "Udine",
    "country_id": "107"
  }, {
    "id": "1893",
    "name": "Umbria",
    "country_id": "107"
  }, {
    "id": "1894",
    "name": "Valle d'Aosta",
    "country_id": "107"
  }, {
    "id": "1895",
    "name": "Varese",
    "country_id": "107"
  }, {
    "id": "1896",
    "name": "Veneto",
    "country_id": "107"
  }, {
    "id": "1897",
    "name": "Venezia",
    "country_id": "107"
  }, {
    "id": "1898",
    "name": "Verbano-Cusio-Ossola",
    "country_id": "107"
  }, {
    "id": "1899",
    "name": "Vercelli",
    "country_id": "107"
  }, {
    "id": "1900",
    "name": "Verona",
    "country_id": "107"
  }, {
    "id": "1901",
    "name": "Vicenza",
    "country_id": "107"
  }, {
    "id": "1902",
    "name": "Viterbo",
    "country_id": "107"
  }, {
    "id": "1903",
    "name": "Buxoro Viloyati",
    "country_id": "108"
  }, {
    "id": "1904",
    "name": "Clarendon",
    "country_id": "108"
  }, {
    "id": "1905",
    "name": "Hanover",
    "country_id": "108"
  }, {
    "id": "1906",
    "name": "Kingston",
    "country_id": "108"
  }, {
    "id": "1907",
    "name": "Manchester",
    "country_id": "108"
  }, {
    "id": "1908",
    "name": "Portland",
    "country_id": "108"
  }, {
    "id": "1909",
    "name": "Saint Andrews",
    "country_id": "108"
  }, {
    "id": "1910",
    "name": "Saint Ann",
    "country_id": "108"
  }, {
    "id": "1911",
    "name": "Saint Catherine",
    "country_id": "108"
  }, {
    "id": "1912",
    "name": "Saint Elizabeth",
    "country_id": "108"
  }, {
    "id": "1913",
    "name": "Saint James",
    "country_id": "108"
  }, {
    "id": "1914",
    "name": "Saint Mary",
    "country_id": "108"
  }, {
    "id": "1915",
    "name": "Saint Thomas",
    "country_id": "108"
  }, {
    "id": "1916",
    "name": "Trelawney",
    "country_id": "108"
  }, {
    "id": "1917",
    "name": "Westmoreland",
    "country_id": "108"
  }, {
    "id": "1918",
    "name": "Aichi",
    "country_id": "109"
  }, {
    "id": "1919",
    "name": "Akita",
    "country_id": "109"
  }, {
    "id": "1920",
    "name": "Aomori",
    "country_id": "109"
  }, {
    "id": "1921",
    "name": "Chiba",
    "country_id": "109"
  }, {
    "id": "1922",
    "name": "Ehime",
    "country_id": "109"
  }, {
    "id": "1923",
    "name": "Fukui",
    "country_id": "109"
  }, {
    "id": "1924",
    "name": "Fukuoka",
    "country_id": "109"
  }, {
    "id": "1925",
    "name": "Fukushima",
    "country_id": "109"
  }, {
    "id": "1926",
    "name": "Gifu",
    "country_id": "109"
  }, {
    "id": "1927",
    "name": "Gumma",
    "country_id": "109"
  }, {
    "id": "1928",
    "name": "Hiroshima",
    "country_id": "109"
  }, {
    "id": "1929",
    "name": "Hokkaido",
    "country_id": "109"
  }, {
    "id": "1930",
    "name": "Hyogo",
    "country_id": "109"
  }, {
    "id": "1931",
    "name": "Ibaraki",
    "country_id": "109"
  }, {
    "id": "1932",
    "name": "Ishikawa",
    "country_id": "109"
  }, {
    "id": "1933",
    "name": "Iwate",
    "country_id": "109"
  }, {
    "id": "1934",
    "name": "Kagawa",
    "country_id": "109"
  }, {
    "id": "1935",
    "name": "Kagoshima",
    "country_id": "109"
  }, {
    "id": "1936",
    "name": "Kanagawa",
    "country_id": "109"
  }, {
    "id": "1937",
    "name": "Kanto",
    "country_id": "109"
  }, {
    "id": "1938",
    "name": "Kochi",
    "country_id": "109"
  }, {
    "id": "1939",
    "name": "Kumamoto",
    "country_id": "109"
  }, {
    "id": "1940",
    "name": "Kyoto",
    "country_id": "109"
  }, {
    "id": "1941",
    "name": "Mie",
    "country_id": "109"
  }, {
    "id": "1942",
    "name": "Miyagi",
    "country_id": "109"
  }, {
    "id": "1943",
    "name": "Miyazaki",
    "country_id": "109"
  }, {
    "id": "1944",
    "name": "Nagano",
    "country_id": "109"
  }, {
    "id": "1945",
    "name": "Nagasaki",
    "country_id": "109"
  }, {
    "id": "1946",
    "name": "Nara",
    "country_id": "109"
  }, {
    "id": "1947",
    "name": "Niigata",
    "country_id": "109"
  }, {
    "id": "1948",
    "name": "Oita",
    "country_id": "109"
  }, {
    "id": "1949",
    "name": "Okayama",
    "country_id": "109"
  }, {
    "id": "1950",
    "name": "Okinawa",
    "country_id": "109"
  }, {
    "id": "1951",
    "name": "Osaka",
    "country_id": "109"
  }, {
    "id": "1952",
    "name": "Saga",
    "country_id": "109"
  }, {
    "id": "1953",
    "name": "Saitama",
    "country_id": "109"
  }, {
    "id": "1954",
    "name": "Shiga",
    "country_id": "109"
  }, {
    "id": "1955",
    "name": "Shimane",
    "country_id": "109"
  }, {
    "id": "1956",
    "name": "Shizuoka",
    "country_id": "109"
  }, {
    "id": "1957",
    "name": "Tochigi",
    "country_id": "109"
  }, {
    "id": "1958",
    "name": "Tokushima",
    "country_id": "109"
  }, {
    "id": "1959",
    "name": "Tokyo",
    "country_id": "109"
  }, {
    "id": "1960",
    "name": "Tottori",
    "country_id": "109"
  }, {
    "id": "1961",
    "name": "Toyama",
    "country_id": "109"
  }, {
    "id": "1962",
    "name": "Wakayama",
    "country_id": "109"
  }, {
    "id": "1963",
    "name": "Yamagata",
    "country_id": "109"
  }, {
    "id": "1964",
    "name": "Yamaguchi",
    "country_id": "109"
  }, {
    "id": "1965",
    "name": "Yamanashi",
    "country_id": "109"
  }, {
    "id": "1966",
    "name": "Grouville",
    "country_id": "110"
  }, {
    "id": "1967",
    "name": "Saint Brelade",
    "country_id": "110"
  }, {
    "id": "1968",
    "name": "Saint Clement",
    "country_id": "110"
  }, {
    "id": "1969",
    "name": "Saint Helier",
    "country_id": "110"
  }, {
    "id": "1970",
    "name": "Saint John",
    "country_id": "110"
  }, {
    "id": "1971",
    "name": "Saint Lawrence",
    "country_id": "110"
  }, {
    "id": "1972",
    "name": "Saint Martin",
    "country_id": "110"
  }, {
    "id": "1973",
    "name": "Saint Mary",
    "country_id": "110"
  }, {
    "id": "1974",
    "name": "Saint Peter",
    "country_id": "110"
  }, {
    "id": "1975",
    "name": "Saint Saviour",
    "country_id": "110"
  }, {
    "id": "1976",
    "name": "Trinity",
    "country_id": "110"
  }, {
    "id": "1977",
    "name": "'Ajlun",
    "country_id": "111"
  }, {
    "id": "1978",
    "name": "Amman",
    "country_id": "111"
  }, {
    "id": "1979",
    "name": "Irbid",
    "country_id": "111"
  }, {
    "id": "1980",
    "name": "Jarash",
    "country_id": "111"
  }, {
    "id": "1981",
    "name": "Ma'an",
    "country_id": "111"
  }, {
    "id": "1982",
    "name": "Madaba",
    "country_id": "111"
  }, {
    "id": "1983",
    "name": "al-'Aqabah",
    "country_id": "111"
  }, {
    "id": "1984",
    "name": "al-Balqa'",
    "country_id": "111"
  }, {
    "id": "1985",
    "name": "al-Karak",
    "country_id": "111"
  }, {
    "id": "1986",
    "name": "al-Mafraq",
    "country_id": "111"
  }, {
    "id": "1987",
    "name": "at-Tafilah",
    "country_id": "111"
  }, {
    "id": "1988",
    "name": "az-Zarqa'",
    "country_id": "111"
  }, {
    "id": "1989",
    "name": "Akmecet",
    "country_id": "112"
  }, {
    "id": "1990",
    "name": "Akmola",
    "country_id": "112"
  }, {
    "id": "1991",
    "name": "Aktobe",
    "country_id": "112"
  }, {
    "id": "1992",
    "name": "Almati",
    "country_id": "112"
  }, {
    "id": "1993",
    "name": "Atirau",
    "country_id": "112"
  }, {
    "id": "1994",
    "name": "Batis Kazakstan",
    "country_id": "112"
  }, {
    "id": "1995",
    "name": "Burlinsky Region",
    "country_id": "112"
  }, {
    "id": "1996",
    "name": "Karagandi",
    "country_id": "112"
  }, {
    "id": "1997",
    "name": "Kostanay",
    "country_id": "112"
  }, {
    "id": "1998",
    "name": "Mankistau",
    "country_id": "112"
  }, {
    "id": "1999",
    "name": "Ontustik Kazakstan",
    "country_id": "112"
  }, {
    "id": "2000",
    "name": "Pavlodar",
    "country_id": "112"
  }, {
    "id": "2001",
    "name": "Sigis Kazakstan",
    "country_id": "112"
  }, {
    "id": "2002",
    "name": "Soltustik Kazakstan",
    "country_id": "112"
  }, {
    "id": "2003",
    "name": "Taraz",
    "country_id": "112"
  }, {
    "id": "2004",
    "name": "Central",
    "country_id": "113"
  }, {
    "id": "2005",
    "name": "Coast",
    "country_id": "113"
  }, {
    "id": "2006",
    "name": "Eastern",
    "country_id": "113"
  }, {
    "id": "2007",
    "name": "Nairobi",
    "country_id": "113"
  }, {
    "id": "2008",
    "name": "North Eastern",
    "country_id": "113"
  }, {
    "id": "2009",
    "name": "Nyanza",
    "country_id": "113"
  }, {
    "id": "2010",
    "name": "Rift Valley",
    "country_id": "113"
  }, {
    "id": "2011",
    "name": "Western",
    "country_id": "113"
  }, {
    "id": "2012",
    "name": "Abaiang",
    "country_id": "114"
  }, {
    "id": "2013",
    "name": "Abemana",
    "country_id": "114"
  }, {
    "id": "2014",
    "name": "Aranuka",
    "country_id": "114"
  }, {
    "id": "2015",
    "name": "Arorae",
    "country_id": "114"
  }, {
    "id": "2016",
    "name": "Banaba",
    "country_id": "114"
  }, {
    "id": "2017",
    "name": "Beru",
    "country_id": "114"
  }, {
    "id": "2018",
    "name": "Butaritari",
    "country_id": "114"
  }, {
    "id": "2019",
    "name": "Kiritimati",
    "country_id": "114"
  }, {
    "id": "2020",
    "name": "Kuria",
    "country_id": "114"
  }, {
    "id": "2021",
    "name": "Maiana",
    "country_id": "114"
  }, {
    "id": "2022",
    "name": "Makin",
    "country_id": "114"
  }, {
    "id": "2023",
    "name": "Marakei",
    "country_id": "114"
  }, {
    "id": "2024",
    "name": "Nikunau",
    "country_id": "114"
  }, {
    "id": "2025",
    "name": "Nonouti",
    "country_id": "114"
  }, {
    "id": "2026",
    "name": "Onotoa",
    "country_id": "114"
  }, {
    "id": "2027",
    "name": "Phoenix Islands",
    "country_id": "114"
  }, {
    "id": "2028",
    "name": "Tabiteuea North",
    "country_id": "114"
  }, {
    "id": "2029",
    "name": "Tabiteuea South",
    "country_id": "114"
  }, {
    "id": "2030",
    "name": "Tabuaeran",
    "country_id": "114"
  }, {
    "id": "2031",
    "name": "Tamana",
    "country_id": "114"
  }, {
    "id": "2032",
    "name": "Tarawa North",
    "country_id": "114"
  }, {
    "id": "2033",
    "name": "Tarawa South",
    "country_id": "114"
  }, {
    "id": "2034",
    "name": "Teraina",
    "country_id": "114"
  }, {
    "id": "2035",
    "name": "Chagangdo",
    "country_id": "115"
  }, {
    "id": "2036",
    "name": "Hamgyeongbukto",
    "country_id": "115"
  }, {
    "id": "2037",
    "name": "Hamgyeongnamdo",
    "country_id": "115"
  }, {
    "id": "2038",
    "name": "Hwanghaebukto",
    "country_id": "115"
  }, {
    "id": "2039",
    "name": "Hwanghaenamdo",
    "country_id": "115"
  }, {
    "id": "2040",
    "name": "Kaeseong",
    "country_id": "115"
  }, {
    "id": "2041",
    "name": "Kangweon",
    "country_id": "115"
  }, {
    "id": "2042",
    "name": "Nampo",
    "country_id": "115"
  }, {
    "id": "2043",
    "name": "Pyeonganbukto",
    "country_id": "115"
  }, {
    "id": "2044",
    "name": "Pyeongannamdo",
    "country_id": "115"
  }, {
    "id": "2045",
    "name": "Pyeongyang",
    "country_id": "115"
  }, {
    "id": "2046",
    "name": "Yanggang",
    "country_id": "115"
  }, {
    "id": "2047",
    "name": "Busan",
    "country_id": "116"
  }, {
    "id": "2048",
    "name": "Cheju",
    "country_id": "116"
  }, {
    "id": "2049",
    "name": "Chollabuk",
    "country_id": "116"
  }, {
    "id": "2050",
    "name": "Chollanam",
    "country_id": "116"
  }, {
    "id": "2051",
    "name": "Chungbuk",
    "country_id": "116"
  }, {
    "id": "2052",
    "name": "Chungcheongbuk",
    "country_id": "116"
  }, {
    "id": "2053",
    "name": "Chungcheongnam",
    "country_id": "116"
  }, {
    "id": "2054",
    "name": "Chungnam",
    "country_id": "116"
  }, {
    "id": "2055",
    "name": "Daegu",
    "country_id": "116"
  }, {
    "id": "2056",
    "name": "Gangwon-do",
    "country_id": "116"
  }, {
    "id": "2057",
    "name": "Goyang-si",
    "country_id": "116"
  }, {
    "id": "2058",
    "name": "Gyeonggi-do",
    "country_id": "116"
  }, {
    "id": "2059",
    "name": "Gyeongsang ",
    "country_id": "116"
  }, {
    "id": "2060",
    "name": "Gyeongsangnam-do",
    "country_id": "116"
  }, {
    "id": "2061",
    "name": "Incheon",
    "country_id": "116"
  }, {
    "id": "2062",
    "name": "Jeju-Si",
    "country_id": "116"
  }, {
    "id": "2063",
    "name": "Jeonbuk",
    "country_id": "116"
  }, {
    "id": "2064",
    "name": "Kangweon",
    "country_id": "116"
  }, {
    "id": "2065",
    "name": "Kwangju",
    "country_id": "116"
  }, {
    "id": "2066",
    "name": "Kyeonggi",
    "country_id": "116"
  }, {
    "id": "2067",
    "name": "Kyeongsangbuk",
    "country_id": "116"
  }, {
    "id": "2068",
    "name": "Kyeongsangnam",
    "country_id": "116"
  }, {
    "id": "2069",
    "name": "Kyonggi-do",
    "country_id": "116"
  }, {
    "id": "2070",
    "name": "Kyungbuk-Do",
    "country_id": "116"
  }, {
    "id": "2071",
    "name": "Kyunggi-Do",
    "country_id": "116"
  }, {
    "id": "2072",
    "name": "Kyunggi-do",
    "country_id": "116"
  }, {
    "id": "2073",
    "name": "Pusan",
    "country_id": "116"
  }, {
    "id": "2074",
    "name": "Seoul",
    "country_id": "116"
  }, {
    "id": "2075",
    "name": "Sudogwon",
    "country_id": "116"
  }, {
    "id": "2076",
    "name": "Taegu",
    "country_id": "116"
  }, {
    "id": "2077",
    "name": "Taejeon",
    "country_id": "116"
  }, {
    "id": "2078",
    "name": "Taejon-gwangyoksi",
    "country_id": "116"
  }, {
    "id": "2079",
    "name": "Ulsan",
    "country_id": "116"
  }, {
    "id": "2080",
    "name": "Wonju",
    "country_id": "116"
  }, {
    "id": "2081",
    "name": "gwangyoksi",
    "country_id": "116"
  }, {
    "id": "2082",
    "name": "Al Asimah",
    "country_id": "117"
  }, {
    "id": "2083",
    "name": "Hawalli",
    "country_id": "117"
  }, {
    "id": "2084",
    "name": "Mishref",
    "country_id": "117"
  }, {
    "id": "2085",
    "name": "Qadesiya",
    "country_id": "117"
  }, {
    "id": "2086",
    "name": "Safat",
    "country_id": "117"
  }, {
    "id": "2087",
    "name": "Salmiya",
    "country_id": "117"
  }, {
    "id": "2088",
    "name": "al-Ahmadi",
    "country_id": "117"
  }, {
    "id": "2089",
    "name": "al-Farwaniyah",
    "country_id": "117"
  }, {
    "id": "2090",
    "name": "al-Jahra",
    "country_id": "117"
  }, {
    "id": "2091",
    "name": "al-Kuwayt",
    "country_id": "117"
  }, {
    "id": "2092",
    "name": "Batken",
    "country_id": "118"
  }, {
    "id": "2093",
    "name": "Bishkek",
    "country_id": "118"
  }, {
    "id": "2094",
    "name": "Chui",
    "country_id": "118"
  }, {
    "id": "2095",
    "name": "Issyk-Kul",
    "country_id": "118"
  }, {
    "id": "2096",
    "name": "Jalal-Abad",
    "country_id": "118"
  }, {
    "id": "2097",
    "name": "Naryn",
    "country_id": "118"
  }, {
    "id": "2098",
    "name": "Osh",
    "country_id": "118"
  }, {
    "id": "2099",
    "name": "Talas",
    "country_id": "118"
  }, {
    "id": "2100",
    "name": "Attopu",
    "country_id": "119"
  }, {
    "id": "2101",
    "name": "Bokeo",
    "country_id": "119"
  }, {
    "id": "2102",
    "name": "Bolikhamsay",
    "country_id": "119"
  }, {
    "id": "2103",
    "name": "Champasak",
    "country_id": "119"
  }, {
    "id": "2104",
    "name": "Houaphanh",
    "country_id": "119"
  }, {
    "id": "2105",
    "name": "Khammouane",
    "country_id": "119"
  }, {
    "id": "2106",
    "name": "Luang Nam Tha",
    "country_id": "119"
  }, {
    "id": "2107",
    "name": "Luang Prabang",
    "country_id": "119"
  }, {
    "id": "2108",
    "name": "Oudomxay",
    "country_id": "119"
  }, {
    "id": "2109",
    "name": "Phongsaly",
    "country_id": "119"
  }, {
    "id": "2110",
    "name": "Saravan",
    "country_id": "119"
  }, {
    "id": "2111",
    "name": "Savannakhet",
    "country_id": "119"
  }, {
    "id": "2112",
    "name": "Sekong",
    "country_id": "119"
  }, {
    "id": "2113",
    "name": "Viangchan Prefecture",
    "country_id": "119"
  }, {
    "id": "2114",
    "name": "Viangchan Province",
    "country_id": "119"
  }, {
    "id": "2115",
    "name": "Xaignabury",
    "country_id": "119"
  }, {
    "id": "2116",
    "name": "Xiang Khuang",
    "country_id": "119"
  }, {
    "id": "2117",
    "name": "Aizkraukles",
    "country_id": "120"
  }, {
    "id": "2118",
    "name": "Aluksnes",
    "country_id": "120"
  }, {
    "id": "2119",
    "name": "Balvu",
    "country_id": "120"
  }, {
    "id": "2120",
    "name": "Bauskas",
    "country_id": "120"
  }, {
    "id": "2121",
    "name": "Cesu",
    "country_id": "120"
  }, {
    "id": "2122",
    "name": "Daugavpils",
    "country_id": "120"
  }, {
    "id": "2123",
    "name": "Daugavpils City",
    "country_id": "120"
  }, {
    "id": "2124",
    "name": "Dobeles",
    "country_id": "120"
  }, {
    "id": "2125",
    "name": "Gulbenes",
    "country_id": "120"
  }, {
    "id": "2126",
    "name": "Jekabspils",
    "country_id": "120"
  }, {
    "id": "2127",
    "name": "Jelgava",
    "country_id": "120"
  }, {
    "id": "2128",
    "name": "Jelgavas",
    "country_id": "120"
  }, {
    "id": "2129",
    "name": "Jurmala City",
    "country_id": "120"
  }, {
    "id": "2130",
    "name": "Kraslavas",
    "country_id": "120"
  }, {
    "id": "2131",
    "name": "Kuldigas",
    "country_id": "120"
  }, {
    "id": "2132",
    "name": "Liepaja",
    "country_id": "120"
  }, {
    "id": "2133",
    "name": "Liepajas",
    "country_id": "120"
  }, {
    "id": "2134",
    "name": "Limbazhu",
    "country_id": "120"
  }, {
    "id": "2135",
    "name": "Ludzas",
    "country_id": "120"
  }, {
    "id": "2136",
    "name": "Madonas",
    "country_id": "120"
  }, {
    "id": "2137",
    "name": "Ogres",
    "country_id": "120"
  }, {
    "id": "2138",
    "name": "Preilu",
    "country_id": "120"
  }, {
    "id": "2139",
    "name": "Rezekne",
    "country_id": "120"
  }, {
    "id": "2140",
    "name": "Rezeknes",
    "country_id": "120"
  }, {
    "id": "2141",
    "name": "Riga",
    "country_id": "120"
  }, {
    "id": "2142",
    "name": "Rigas",
    "country_id": "120"
  }, {
    "id": "2143",
    "name": "Saldus",
    "country_id": "120"
  }, {
    "id": "2144",
    "name": "Talsu",
    "country_id": "120"
  }, {
    "id": "2145",
    "name": "Tukuma",
    "country_id": "120"
  }, {
    "id": "2146",
    "name": "Valkas",
    "country_id": "120"
  }, {
    "id": "2147",
    "name": "Valmieras",
    "country_id": "120"
  }, {
    "id": "2148",
    "name": "Ventspils",
    "country_id": "120"
  }, {
    "id": "2149",
    "name": "Ventspils City",
    "country_id": "120"
  }, {
    "id": "2150",
    "name": "Beirut",
    "country_id": "121"
  }, {
    "id": "2151",
    "name": "Jabal Lubnan",
    "country_id": "121"
  }, {
    "id": "2152",
    "name": "Mohafazat Liban-Nord",
    "country_id": "121"
  }, {
    "id": "2153",
    "name": "Mohafazat Mont-Liban",
    "country_id": "121"
  }, {
    "id": "2154",
    "name": "Sidon",
    "country_id": "121"
  }, {
    "id": "2155",
    "name": "al-Biqa",
    "country_id": "121"
  }, {
    "id": "2156",
    "name": "al-Janub",
    "country_id": "121"
  }, {
    "id": "2157",
    "name": "an-Nabatiyah",
    "country_id": "121"
  }, {
    "id": "2158",
    "name": "ash-Shamal",
    "country_id": "121"
  }, {
    "id": "2159",
    "name": "Berea",
    "country_id": "122"
  }, {
    "id": "2160",
    "name": "Butha-Buthe",
    "country_id": "122"
  }, {
    "id": "2161",
    "name": "Leribe",
    "country_id": "122"
  }, {
    "id": "2162",
    "name": "Mafeteng",
    "country_id": "122"
  }, {
    "id": "2163",
    "name": "Maseru",
    "country_id": "122"
  }, {
    "id": "2164",
    "name": "Mohale's Hoek",
    "country_id": "122"
  }, {
    "id": "2165",
    "name": "Mokhotlong",
    "country_id": "122"
  }, {
    "id": "2166",
    "name": "Qacha's Nek",
    "country_id": "122"
  }, {
    "id": "2167",
    "name": "Quthing",
    "country_id": "122"
  }, {
    "id": "2168",
    "name": "Thaba-Tseka",
    "country_id": "122"
  }, {
    "id": "2169",
    "name": "Bomi",
    "country_id": "123"
  }, {
    "id": "2170",
    "name": "Bong",
    "country_id": "123"
  }, {
    "id": "2171",
    "name": "Grand Bassa",
    "country_id": "123"
  }, {
    "id": "2172",
    "name": "Grand Cape Mount",
    "country_id": "123"
  }, {
    "id": "2173",
    "name": "Grand Gedeh",
    "country_id": "123"
  }, {
    "id": "2174",
    "name": "Loffa",
    "country_id": "123"
  }, {
    "id": "2175",
    "name": "Margibi",
    "country_id": "123"
  }, {
    "id": "2176",
    "name": "Maryland and Grand Kru",
    "country_id": "123"
  }, {
    "id": "2177",
    "name": "Montserrado",
    "country_id": "123"
  }, {
    "id": "2178",
    "name": "Nimba",
    "country_id": "123"
  }, {
    "id": "2179",
    "name": "Rivercess",
    "country_id": "123"
  }, {
    "id": "2180",
    "name": "Sinoe",
    "country_id": "123"
  }, {
    "id": "2181",
    "name": "Ajdabiya",
    "country_id": "124"
  }, {
    "id": "2182",
    "name": "Fezzan",
    "country_id": "124"
  }, {
    "id": "2183",
    "name": "Banghazi",
    "country_id": "124"
  }, {
    "id": "2184",
    "name": "Darnah",
    "country_id": "124"
  }, {
    "id": "2185",
    "name": "Ghadamis",
    "country_id": "124"
  }, {
    "id": "2186",
    "name": "Gharyan",
    "country_id": "124"
  }, {
    "id": "2187",
    "name": "Misratah",
    "country_id": "124"
  }, {
    "id": "2188",
    "name": "Murzuq",
    "country_id": "124"
  }, {
    "id": "2189",
    "name": "Sabha",
    "country_id": "124"
  }, {
    "id": "2190",
    "name": "Sawfajjin",
    "country_id": "124"
  }, {
    "id": "2191",
    "name": "Surt",
    "country_id": "124"
  }, {
    "id": "2192",
    "name": "Tarabulus",
    "country_id": "124"
  }, {
    "id": "2193",
    "name": "Tarhunah",
    "country_id": "124"
  }, {
    "id": "2194",
    "name": "Tripolitania",
    "country_id": "124"
  }, {
    "id": "2195",
    "name": "Tubruq",
    "country_id": "124"
  }, {
    "id": "2196",
    "name": "Yafran",
    "country_id": "124"
  }, {
    "id": "2197",
    "name": "Zlitan",
    "country_id": "124"
  }, {
    "id": "2198",
    "name": "al-'Aziziyah",
    "country_id": "124"
  }, {
    "id": "2199",
    "name": "al-Fatih",
    "country_id": "124"
  }, {
    "id": "2200",
    "name": "al-Jabal al Akhdar",
    "country_id": "124"
  }, {
    "id": "2201",
    "name": "al-Jufrah",
    "country_id": "124"
  }, {
    "id": "2202",
    "name": "al-Khums",
    "country_id": "124"
  }, {
    "id": "2203",
    "name": "al-Kufrah",
    "country_id": "124"
  }, {
    "id": "2204",
    "name": "an-Nuqat al-Khams",
    "country_id": "124"
  }, {
    "id": "2205",
    "name": "ash-Shati'",
    "country_id": "124"
  }, {
    "id": "2206",
    "name": "az-Zawiyah",
    "country_id": "124"
  }, {
    "id": "2207",
    "name": "Balzers",
    "country_id": "125"
  }, {
    "id": "2208",
    "name": "Eschen",
    "country_id": "125"
  }, {
    "id": "2209",
    "name": "Gamprin",
    "country_id": "125"
  }, {
    "id": "2210",
    "name": "Mauren",
    "country_id": "125"
  }, {
    "id": "2211",
    "name": "Planken",
    "country_id": "125"
  }, {
    "id": "2212",
    "name": "Ruggell",
    "country_id": "125"
  }, {
    "id": "2213",
    "name": "Schaan",
    "country_id": "125"
  }, {
    "id": "2214",
    "name": "Schellenberg",
    "country_id": "125"
  }, {
    "id": "2215",
    "name": "Triesen",
    "country_id": "125"
  }, {
    "id": "2216",
    "name": "Triesenberg",
    "country_id": "125"
  }, {
    "id": "2217",
    "name": "Vaduz",
    "country_id": "125"
  }, {
    "id": "2218",
    "name": "Alytaus",
    "country_id": "126"
  }, {
    "id": "2219",
    "name": "Anyksciai",
    "country_id": "126"
  }, {
    "id": "2220",
    "name": "Kauno",
    "country_id": "126"
  }, {
    "id": "2221",
    "name": "Klaipedos",
    "country_id": "126"
  }, {
    "id": "2222",
    "name": "Marijampoles",
    "country_id": "126"
  }, {
    "id": "2223",
    "name": "Panevezhio",
    "country_id": "126"
  }, {
    "id": "2224",
    "name": "Panevezys",
    "country_id": "126"
  }, {
    "id": "2225",
    "name": "Shiauliu",
    "country_id": "126"
  }, {
    "id": "2226",
    "name": "Taurages",
    "country_id": "126"
  }, {
    "id": "2227",
    "name": "Telshiu",
    "country_id": "126"
  }, {
    "id": "2228",
    "name": "Telsiai",
    "country_id": "126"
  }, {
    "id": "2229",
    "name": "Utenos",
    "country_id": "126"
  }, {
    "id": "2230",
    "name": "Vilniaus",
    "country_id": "126"
  }, {
    "id": "2231",
    "name": "Capellen",
    "country_id": "127"
  }, {
    "id": "2232",
    "name": "Clervaux",
    "country_id": "127"
  }, {
    "id": "2233",
    "name": "Diekirch",
    "country_id": "127"
  }, {
    "id": "2234",
    "name": "Echternach",
    "country_id": "127"
  }, {
    "id": "2235",
    "name": "Esch-sur-Alzette",
    "country_id": "127"
  }, {
    "id": "2236",
    "name": "Grevenmacher",
    "country_id": "127"
  }, {
    "id": "2237",
    "name": "Luxembourg",
    "country_id": "127"
  }, {
    "id": "2238",
    "name": "Mersch",
    "country_id": "127"
  }, {
    "id": "2239",
    "name": "Redange",
    "country_id": "127"
  }, {
    "id": "2240",
    "name": "Remich",
    "country_id": "127"
  }, {
    "id": "2241",
    "name": "Vianden",
    "country_id": "127"
  }, {
    "id": "2242",
    "name": "Wiltz",
    "country_id": "127"
  }, {
    "id": "2243",
    "name": "Macau",
    "country_id": "128"
  }, {
    "id": "2244",
    "name": "Berovo",
    "country_id": "129"
  }, {
    "id": "2245",
    "name": "Bitola",
    "country_id": "129"
  }, {
    "id": "2246",
    "name": "Brod",
    "country_id": "129"
  }, {
    "id": "2247",
    "name": "Debar",
    "country_id": "129"
  }, {
    "id": "2248",
    "name": "Delchevo",
    "country_id": "129"
  }, {
    "id": "2249",
    "name": "Demir Hisar",
    "country_id": "129"
  }, {
    "id": "2250",
    "name": "Gevgelija",
    "country_id": "129"
  }, {
    "id": "2251",
    "name": "Gostivar",
    "country_id": "129"
  }, {
    "id": "2252",
    "name": "Kavadarci",
    "country_id": "129"
  }, {
    "id": "2253",
    "name": "Kichevo",
    "country_id": "129"
  }, {
    "id": "2254",
    "name": "Kochani",
    "country_id": "129"
  }, {
    "id": "2255",
    "name": "Kratovo",
    "country_id": "129"
  }, {
    "id": "2256",
    "name": "Kriva Palanka",
    "country_id": "129"
  }, {
    "id": "2257",
    "name": "Krushevo",
    "country_id": "129"
  }, {
    "id": "2258",
    "name": "Kumanovo",
    "country_id": "129"
  }, {
    "id": "2259",
    "name": "Negotino",
    "country_id": "129"
  }, {
    "id": "2260",
    "name": "Ohrid",
    "country_id": "129"
  }, {
    "id": "2261",
    "name": "Prilep",
    "country_id": "129"
  }, {
    "id": "2262",
    "name": "Probishtip",
    "country_id": "129"
  }, {
    "id": "2263",
    "name": "Radovish",
    "country_id": "129"
  }, {
    "id": "2264",
    "name": "Resen",
    "country_id": "129"
  }, {
    "id": "2265",
    "name": "Shtip",
    "country_id": "129"
  }, {
    "id": "2266",
    "name": "Skopje",
    "country_id": "129"
  }, {
    "id": "2267",
    "name": "Struga",
    "country_id": "129"
  }, {
    "id": "2268",
    "name": "Strumica",
    "country_id": "129"
  }, {
    "id": "2269",
    "name": "Sveti Nikole",
    "country_id": "129"
  }, {
    "id": "2270",
    "name": "Tetovo",
    "country_id": "129"
  }, {
    "id": "2271",
    "name": "Valandovo",
    "country_id": "129"
  }, {
    "id": "2272",
    "name": "Veles",
    "country_id": "129"
  }, {
    "id": "2273",
    "name": "Vinica",
    "country_id": "129"
  }, {
    "id": "2274",
    "name": "Antananarivo",
    "country_id": "130"
  }, {
    "id": "2275",
    "name": "Antsiranana",
    "country_id": "130"
  }, {
    "id": "2276",
    "name": "Fianarantsoa",
    "country_id": "130"
  }, {
    "id": "2277",
    "name": "Mahajanga",
    "country_id": "130"
  }, {
    "id": "2278",
    "name": "Toamasina",
    "country_id": "130"
  }, {
    "id": "2279",
    "name": "Toliary",
    "country_id": "130"
  }, {
    "id": "2280",
    "name": "Balaka",
    "country_id": "131"
  }, {
    "id": "2281",
    "name": "Blantyre City",
    "country_id": "131"
  }, {
    "id": "2282",
    "name": "Chikwawa",
    "country_id": "131"
  }, {
    "id": "2283",
    "name": "Chiradzulu",
    "country_id": "131"
  }, {
    "id": "2284",
    "name": "Chitipa",
    "country_id": "131"
  }, {
    "id": "2285",
    "name": "Dedza",
    "country_id": "131"
  }, {
    "id": "2286",
    "name": "Dowa",
    "country_id": "131"
  }, {
    "id": "2287",
    "name": "Karonga",
    "country_id": "131"
  }, {
    "id": "2288",
    "name": "Kasungu",
    "country_id": "131"
  }, {
    "id": "2289",
    "name": "Lilongwe City",
    "country_id": "131"
  }, {
    "id": "2290",
    "name": "Machinga",
    "country_id": "131"
  }, {
    "id": "2291",
    "name": "Mangochi",
    "country_id": "131"
  }, {
    "id": "2292",
    "name": "Mchinji",
    "country_id": "131"
  }, {
    "id": "2293",
    "name": "Mulanje",
    "country_id": "131"
  }, {
    "id": "2294",
    "name": "Mwanza",
    "country_id": "131"
  }, {
    "id": "2295",
    "name": "Mzimba",
    "country_id": "131"
  }, {
    "id": "2296",
    "name": "Mzuzu City",
    "country_id": "131"
  }, {
    "id": "2297",
    "name": "Nkhata Bay",
    "country_id": "131"
  }, {
    "id": "2298",
    "name": "Nkhotakota",
    "country_id": "131"
  }, {
    "id": "2299",
    "name": "Nsanje",
    "country_id": "131"
  }, {
    "id": "2300",
    "name": "Ntcheu",
    "country_id": "131"
  }, {
    "id": "2301",
    "name": "Ntchisi",
    "country_id": "131"
  }, {
    "id": "2302",
    "name": "Phalombe",
    "country_id": "131"
  }, {
    "id": "2303",
    "name": "Rumphi",
    "country_id": "131"
  }, {
    "id": "2304",
    "name": "Salima",
    "country_id": "131"
  }, {
    "id": "2305",
    "name": "Thyolo",
    "country_id": "131"
  }, {
    "id": "2306",
    "name": "Zomba Municipality",
    "country_id": "131"
  }, {
    "id": "2307",
    "name": "Johor",
    "country_id": "132"
  }, {
    "id": "2308",
    "name": "Kedah",
    "country_id": "132"
  }, {
    "id": "2309",
    "name": "Kelantan",
    "country_id": "132"
  }, {
    "id": "2310",
    "name": "Kuala Lumpur",
    "country_id": "132"
  }, {
    "id": "2311",
    "name": "Labuan",
    "country_id": "132"
  }, {
    "id": "2312",
    "name": "Melaka",
    "country_id": "132"
  }, {
    "id": "2313",
    "name": "Negeri Johor",
    "country_id": "132"
  }, {
    "id": "2314",
    "name": "Negeri Sembilan",
    "country_id": "132"
  }, {
    "id": "2315",
    "name": "Pahang",
    "country_id": "132"
  }, {
    "id": "2316",
    "name": "Penang",
    "country_id": "132"
  }, {
    "id": "2317",
    "name": "Perak",
    "country_id": "132"
  }, {
    "id": "2318",
    "name": "Perlis",
    "country_id": "132"
  }, {
    "id": "2319",
    "name": "Pulau Pinang",
    "country_id": "132"
  }, {
    "id": "2320",
    "name": "Sabah",
    "country_id": "132"
  }, {
    "id": "2321",
    "name": "Sarawak",
    "country_id": "132"
  }, {
    "id": "2322",
    "name": "Selangor",
    "country_id": "132"
  }, {
    "id": "2323",
    "name": "Sembilan",
    "country_id": "132"
  }, {
    "id": "2324",
    "name": "Terengganu",
    "country_id": "132"
  }, {
    "id": "2325",
    "name": "Alif Alif",
    "country_id": "133"
  }, {
    "id": "2326",
    "name": "Alif Dhaal",
    "country_id": "133"
  }, {
    "id": "2327",
    "name": "Baa",
    "country_id": "133"
  }, {
    "id": "2328",
    "name": "Dhaal",
    "country_id": "133"
  }, {
    "id": "2329",
    "name": "Faaf",
    "country_id": "133"
  }, {
    "id": "2330",
    "name": "Gaaf Alif",
    "country_id": "133"
  }, {
    "id": "2331",
    "name": "Gaaf Dhaal",
    "country_id": "133"
  }, {
    "id": "2332",
    "name": "Ghaviyani",
    "country_id": "133"
  }, {
    "id": "2333",
    "name": "Haa Alif",
    "country_id": "133"
  }, {
    "id": "2334",
    "name": "Haa Dhaal",
    "country_id": "133"
  }, {
    "id": "2335",
    "name": "Kaaf",
    "country_id": "133"
  }, {
    "id": "2336",
    "name": "Laam",
    "country_id": "133"
  }, {
    "id": "2337",
    "name": "Lhaviyani",
    "country_id": "133"
  }, {
    "id": "2338",
    "name": "Male",
    "country_id": "133"
  }, {
    "id": "2339",
    "name": "Miim",
    "country_id": "133"
  }, {
    "id": "2340",
    "name": "Nuun",
    "country_id": "133"
  }, {
    "id": "2341",
    "name": "Raa",
    "country_id": "133"
  }, {
    "id": "2342",
    "name": "Shaviyani",
    "country_id": "133"
  }, {
    "id": "2343",
    "name": "Siin",
    "country_id": "133"
  }, {
    "id": "2344",
    "name": "Thaa",
    "country_id": "133"
  }, {
    "id": "2345",
    "name": "Vaav",
    "country_id": "133"
  }, {
    "id": "2346",
    "name": "Bamako",
    "country_id": "134"
  }, {
    "id": "2347",
    "name": "Gao",
    "country_id": "134"
  }, {
    "id": "2348",
    "name": "Kayes",
    "country_id": "134"
  }, {
    "id": "2349",
    "name": "Kidal",
    "country_id": "134"
  }, {
    "id": "2350",
    "name": "Koulikoro",
    "country_id": "134"
  }, {
    "id": "2351",
    "name": "Mopti",
    "country_id": "134"
  }, {
    "id": "2352",
    "name": "Segou",
    "country_id": "134"
  }, {
    "id": "2353",
    "name": "Sikasso",
    "country_id": "134"
  }, {
    "id": "2354",
    "name": "Tombouctou",
    "country_id": "134"
  }, {
    "id": "2355",
    "name": "Gozo and Comino",
    "country_id": "135"
  }, {
    "id": "2356",
    "name": "Inner Harbour",
    "country_id": "135"
  }, {
    "id": "2357",
    "name": "Northern",
    "country_id": "135"
  }, {
    "id": "2358",
    "name": "Outer Harbour",
    "country_id": "135"
  }, {
    "id": "2359",
    "name": "South Eastern",
    "country_id": "135"
  }, {
    "id": "2360",
    "name": "Valletta",
    "country_id": "135"
  }, {
    "id": "2361",
    "name": "Western",
    "country_id": "135"
  }, {
    "id": "2362",
    "name": "Castletown",
    "country_id": "136"
  }, {
    "id": "2363",
    "name": "Douglas",
    "country_id": "136"
  }, {
    "id": "2364",
    "name": "Laxey",
    "country_id": "136"
  }, {
    "id": "2365",
    "name": "Onchan",
    "country_id": "136"
  }, {
    "id": "2366",
    "name": "Peel",
    "country_id": "136"
  }, {
    "id": "2367",
    "name": "Port Erin",
    "country_id": "136"
  }, {
    "id": "2368",
    "name": "Port Saint Mary",
    "country_id": "136"
  }, {
    "id": "2369",
    "name": "Ramsey",
    "country_id": "136"
  }, {
    "id": "2370",
    "name": "Ailinlaplap",
    "country_id": "137"
  }, {
    "id": "2371",
    "name": "Ailuk",
    "country_id": "137"
  }, {
    "id": "2372",
    "name": "Arno",
    "country_id": "137"
  }, {
    "id": "2373",
    "name": "Aur",
    "country_id": "137"
  }, {
    "id": "2374",
    "name": "Bikini",
    "country_id": "137"
  }, {
    "id": "2375",
    "name": "Ebon",
    "country_id": "137"
  }, {
    "id": "2376",
    "name": "Enewetak",
    "country_id": "137"
  }, {
    "id": "2377",
    "name": "Jabat",
    "country_id": "137"
  }, {
    "id": "2378",
    "name": "Jaluit",
    "country_id": "137"
  }, {
    "id": "2379",
    "name": "Kili",
    "country_id": "137"
  }, {
    "id": "2380",
    "name": "Kwajalein",
    "country_id": "137"
  }, {
    "id": "2381",
    "name": "Lae",
    "country_id": "137"
  }, {
    "id": "2382",
    "name": "Lib",
    "country_id": "137"
  }, {
    "id": "2383",
    "name": "Likiep",
    "country_id": "137"
  }, {
    "id": "2384",
    "name": "Majuro",
    "country_id": "137"
  }, {
    "id": "2385",
    "name": "Maloelap",
    "country_id": "137"
  }, {
    "id": "2386",
    "name": "Mejit",
    "country_id": "137"
  }, {
    "id": "2387",
    "name": "Mili",
    "country_id": "137"
  }, {
    "id": "2388",
    "name": "Namorik",
    "country_id": "137"
  }, {
    "id": "2389",
    "name": "Namu",
    "country_id": "137"
  }, {
    "id": "2390",
    "name": "Rongelap",
    "country_id": "137"
  }, {
    "id": "2391",
    "name": "Ujae",
    "country_id": "137"
  }, {
    "id": "2392",
    "name": "Utrik",
    "country_id": "137"
  }, {
    "id": "2393",
    "name": "Wotho",
    "country_id": "137"
  }, {
    "id": "2394",
    "name": "Wotje",
    "country_id": "137"
  }, {
    "id": "2395",
    "name": "Fort-de-France",
    "country_id": "138"
  }, {
    "id": "2396",
    "name": "La Trinite",
    "country_id": "138"
  }, {
    "id": "2397",
    "name": "Le Marin",
    "country_id": "138"
  }, {
    "id": "2398",
    "name": "Saint-Pierre",
    "country_id": "138"
  }, {
    "id": "2399",
    "name": "Adrar",
    "country_id": "139"
  }, {
    "id": "2400",
    "name": "Assaba",
    "country_id": "139"
  }, {
    "id": "2401",
    "name": "Brakna",
    "country_id": "139"
  }, {
    "id": "2402",
    "name": "Dhakhlat Nawadibu",
    "country_id": "139"
  }, {
    "id": "2403",
    "name": "Hudh-al-Gharbi",
    "country_id": "139"
  }, {
    "id": "2404",
    "name": "Hudh-ash-Sharqi",
    "country_id": "139"
  }, {
    "id": "2405",
    "name": "Inshiri",
    "country_id": "139"
  }, {
    "id": "2406",
    "name": "Nawakshut",
    "country_id": "139"
  }, {
    "id": "2407",
    "name": "Qidimagha",
    "country_id": "139"
  }, {
    "id": "2408",
    "name": "Qurqul",
    "country_id": "139"
  }, {
    "id": "2409",
    "name": "Taqant",
    "country_id": "139"
  }, {
    "id": "2410",
    "name": "Tiris Zammur",
    "country_id": "139"
  }, {
    "id": "2411",
    "name": "Trarza",
    "country_id": "139"
  }, {
    "id": "2412",
    "name": "Black River",
    "country_id": "140"
  }, {
    "id": "2413",
    "name": "Eau Coulee",
    "country_id": "140"
  }, {
    "id": "2414",
    "name": "Flacq",
    "country_id": "140"
  }, {
    "id": "2415",
    "name": "Floreal",
    "country_id": "140"
  }, {
    "id": "2416",
    "name": "Grand Port",
    "country_id": "140"
  }, {
    "id": "2417",
    "name": "Moka",
    "country_id": "140"
  }, {
    "id": "2418",
    "name": "Pamplempousses",
    "country_id": "140"
  }, {
    "id": "2419",
    "name": "Plaines Wilhelm",
    "country_id": "140"
  }, {
    "id": "2420",
    "name": "Port Louis",
    "country_id": "140"
  }, {
    "id": "2421",
    "name": "Riviere du Rempart",
    "country_id": "140"
  }, {
    "id": "2422",
    "name": "Rodrigues",
    "country_id": "140"
  }, {
    "id": "2423",
    "name": "Rose Hill",
    "country_id": "140"
  }, {
    "id": "2424",
    "name": "Savanne",
    "country_id": "140"
  }, {
    "id": "2425",
    "name": "Mayotte",
    "country_id": "141"
  }, {
    "id": "2426",
    "name": "Pamanzi",
    "country_id": "141"
  }, {
    "id": "2427",
    "name": "Aguascalientes",
    "country_id": "142"
  }, {
    "id": "2428",
    "name": "Baja California",
    "country_id": "142"
  }, {
    "id": "2429",
    "name": "Baja California Sur",
    "country_id": "142"
  }, {
    "id": "2430",
    "name": "Campeche",
    "country_id": "142"
  }, {
    "id": "2431",
    "name": "Chiapas",
    "country_id": "142"
  }, {
    "id": "2432",
    "name": "Chihuahua",
    "country_id": "142"
  }, {
    "id": "2433",
    "name": "Coahuila",
    "country_id": "142"
  }, {
    "id": "2434",
    "name": "Colima",
    "country_id": "142"
  }, {
    "id": "2435",
    "name": "Distrito Federal",
    "country_id": "142"
  }, {
    "id": "2436",
    "name": "Durango",
    "country_id": "142"
  }, {
    "id": "2437",
    "name": "Estado de Mexico",
    "country_id": "142"
  }, {
    "id": "2438",
    "name": "Guanajuato",
    "country_id": "142"
  }, {
    "id": "2439",
    "name": "Guerrero",
    "country_id": "142"
  }, {
    "id": "2440",
    "name": "Hidalgo",
    "country_id": "142"
  }, {
    "id": "2441",
    "name": "Jalisco",
    "country_id": "142"
  }, {
    "id": "2442",
    "name": "Mexico",
    "country_id": "142"
  }, {
    "id": "2443",
    "name": "Michoacan",
    "country_id": "142"
  }, {
    "id": "2444",
    "name": "Morelos",
    "country_id": "142"
  }, {
    "id": "2445",
    "name": "Nayarit",
    "country_id": "142"
  }, {
    "id": "2446",
    "name": "Nuevo Leon",
    "country_id": "142"
  }, {
    "id": "2447",
    "name": "Oaxaca",
    "country_id": "142"
  }, {
    "id": "2448",
    "name": "Puebla",
    "country_id": "142"
  }, {
    "id": "2449",
    "name": "Queretaro",
    "country_id": "142"
  }, {
    "id": "2450",
    "name": "Quintana Roo",
    "country_id": "142"
  }, {
    "id": "2451",
    "name": "San Luis Potosi",
    "country_id": "142"
  }, {
    "id": "2452",
    "name": "Sinaloa",
    "country_id": "142"
  }, {
    "id": "2453",
    "name": "Sonora",
    "country_id": "142"
  }, {
    "id": "2454",
    "name": "Tabasco",
    "country_id": "142"
  }, {
    "id": "2455",
    "name": "Tamaulipas",
    "country_id": "142"
  }, {
    "id": "2456",
    "name": "Tlaxcala",
    "country_id": "142"
  }, {
    "id": "2457",
    "name": "Veracruz",
    "country_id": "142"
  }, {
    "id": "2458",
    "name": "Yucatan",
    "country_id": "142"
  }, {
    "id": "2459",
    "name": "Zacatecas",
    "country_id": "142"
  }, {
    "id": "2460",
    "name": "Chuuk",
    "country_id": "143"
  }, {
    "id": "2461",
    "name": "Kusaie",
    "country_id": "143"
  }, {
    "id": "2462",
    "name": "Pohnpei",
    "country_id": "143"
  }, {
    "id": "2463",
    "name": "Yap",
    "country_id": "143"
  }, {
    "id": "2464",
    "name": "Balti",
    "country_id": "144"
  }, {
    "id": "2465",
    "name": "Cahul",
    "country_id": "144"
  }, {
    "id": "2466",
    "name": "Chisinau",
    "country_id": "144"
  }, {
    "id": "2467",
    "name": "Chisinau Oras",
    "country_id": "144"
  }, {
    "id": "2468",
    "name": "Edinet",
    "country_id": "144"
  }, {
    "id": "2469",
    "name": "Gagauzia",
    "country_id": "144"
  }, {
    "id": "2470",
    "name": "Lapusna",
    "country_id": "144"
  }, {
    "id": "2471",
    "name": "Orhei",
    "country_id": "144"
  }, {
    "id": "2472",
    "name": "Soroca",
    "country_id": "144"
  }, {
    "id": "2473",
    "name": "Taraclia",
    "country_id": "144"
  }, {
    "id": "2474",
    "name": "Tighina",
    "country_id": "144"
  }, {
    "id": "2475",
    "name": "Transnistria",
    "country_id": "144"
  }, {
    "id": "2476",
    "name": "Ungheni",
    "country_id": "144"
  }, {
    "id": "2477",
    "name": "Fontvieille",
    "country_id": "145"
  }, {
    "id": "2478",
    "name": "La Condamine",
    "country_id": "145"
  }, {
    "id": "2479",
    "name": "Monaco-Ville",
    "country_id": "145"
  }, {
    "id": "2480",
    "name": "Monte Carlo",
    "country_id": "145"
  }, {
    "id": "2481",
    "name": "Arhangaj",
    "country_id": "146"
  }, {
    "id": "2482",
    "name": "Bajan-Olgij",
    "country_id": "146"
  }, {
    "id": "2483",
    "name": "Bajanhongor",
    "country_id": "146"
  }, {
    "id": "2484",
    "name": "Bulgan",
    "country_id": "146"
  }, {
    "id": "2485",
    "name": "Darhan-Uul",
    "country_id": "146"
  }, {
    "id": "2486",
    "name": "Dornod",
    "country_id": "146"
  }, {
    "id": "2487",
    "name": "Dornogovi",
    "country_id": "146"
  }, {
    "id": "2488",
    "name": "Dundgovi",
    "country_id": "146"
  }, {
    "id": "2489",
    "name": "Govi-Altaj",
    "country_id": "146"
  }, {
    "id": "2490",
    "name": "Govisumber",
    "country_id": "146"
  }, {
    "id": "2491",
    "name": "Hentij",
    "country_id": "146"
  }, {
    "id": "2492",
    "name": "Hovd",
    "country_id": "146"
  }, {
    "id": "2493",
    "name": "Hovsgol",
    "country_id": "146"
  }, {
    "id": "2494",
    "name": "Omnogovi",
    "country_id": "146"
  }, {
    "id": "2495",
    "name": "Orhon",
    "country_id": "146"
  }, {
    "id": "2496",
    "name": "Ovorhangaj",
    "country_id": "146"
  }, {
    "id": "2497",
    "name": "Selenge",
    "country_id": "146"
  }, {
    "id": "2498",
    "name": "Suhbaatar",
    "country_id": "146"
  }, {
    "id": "2499",
    "name": "Tov",
    "country_id": "146"
  }, {
    "id": "2500",
    "name": "Ulaanbaatar",
    "country_id": "146"
  }, {
    "id": "2501",
    "name": "Uvs",
    "country_id": "146"
  }, {
    "id": "2502",
    "name": "Zavhan",
    "country_id": "146"
  }, {
    "id": "2503",
    "name": "Montserrat",
    "country_id": "147"
  }, {
    "id": "2504",
    "name": "Agadir",
    "country_id": "148"
  }, {
    "id": "2505",
    "name": "Casablanca",
    "country_id": "148"
  }, {
    "id": "2506",
    "name": "Chaouia-Ouardigha",
    "country_id": "148"
  }, {
    "id": "2507",
    "name": "Doukkala-Abda",
    "country_id": "148"
  }, {
    "id": "2508",
    "name": "Fes-Boulemane",
    "country_id": "148"
  }, {
    "id": "2509",
    "name": "Gharb-Chrarda-Beni Hssen",
    "country_id": "148"
  }, {
    "id": "2510",
    "name": "Guelmim",
    "country_id": "148"
  }, {
    "id": "2511",
    "name": "Kenitra",
    "country_id": "148"
  }, {
    "id": "2512",
    "name": "Marrakech-Tensift-Al Haouz",
    "country_id": "148"
  }, {
    "id": "2513",
    "name": "Meknes-Tafilalet",
    "country_id": "148"
  }, {
    "id": "2514",
    "name": "Oriental",
    "country_id": "148"
  }, {
    "id": "2515",
    "name": "Oujda",
    "country_id": "148"
  }, {
    "id": "2516",
    "name": "Province de Tanger",
    "country_id": "148"
  }, {
    "id": "2517",
    "name": "Rabat-Sale-Zammour-Zaer",
    "country_id": "148"
  }, {
    "id": "2518",
    "name": "Sala Al Jadida",
    "country_id": "148"
  }, {
    "id": "2519",
    "name": "Settat",
    "country_id": "148"
  }, {
    "id": "2520",
    "name": "Souss Massa-Draa",
    "country_id": "148"
  }, {
    "id": "2521",
    "name": "Tadla-Azilal",
    "country_id": "148"
  }, {
    "id": "2522",
    "name": "Tangier-Tetouan",
    "country_id": "148"
  }, {
    "id": "2523",
    "name": "Taza-Al Hoceima-Taounate",
    "country_id": "148"
  }, {
    "id": "2524",
    "name": "Wilaya de Casablanca",
    "country_id": "148"
  }, {
    "id": "2525",
    "name": "Wilaya de Rabat-Sale",
    "country_id": "148"
  }, {
    "id": "2526",
    "name": "Cabo Delgado",
    "country_id": "149"
  }, {
    "id": "2527",
    "name": "Gaza",
    "country_id": "149"
  }, {
    "id": "2528",
    "name": "Inhambane",
    "country_id": "149"
  }, {
    "id": "2529",
    "name": "Manica",
    "country_id": "149"
  }, {
    "id": "2530",
    "name": "Maputo",
    "country_id": "149"
  }, {
    "id": "2531",
    "name": "Maputo Provincia",
    "country_id": "149"
  }, {
    "id": "2532",
    "name": "Nampula",
    "country_id": "149"
  }, {
    "id": "2533",
    "name": "Niassa",
    "country_id": "149"
  }, {
    "id": "2534",
    "name": "Sofala",
    "country_id": "149"
  }, {
    "id": "2535",
    "name": "Tete",
    "country_id": "149"
  }, {
    "id": "2536",
    "name": "Zambezia",
    "country_id": "149"
  }, {
    "id": "2537",
    "name": "Ayeyarwady",
    "country_id": "150"
  }, {
    "id": "2538",
    "name": "Bago",
    "country_id": "150"
  }, {
    "id": "2539",
    "name": "Chin",
    "country_id": "150"
  }, {
    "id": "2540",
    "name": "Kachin",
    "country_id": "150"
  }, {
    "id": "2541",
    "name": "Kayah",
    "country_id": "150"
  }, {
    "id": "2542",
    "name": "Kayin",
    "country_id": "150"
  }, {
    "id": "2543",
    "name": "Magway",
    "country_id": "150"
  }, {
    "id": "2544",
    "name": "Mandalay",
    "country_id": "150"
  }, {
    "id": "2545",
    "name": "Mon",
    "country_id": "150"
  }, {
    "id": "2546",
    "name": "Nay Pyi Taw",
    "country_id": "150"
  }, {
    "id": "2547",
    "name": "Rakhine",
    "country_id": "150"
  }, {
    "id": "2548",
    "name": "Sagaing",
    "country_id": "150"
  }, {
    "id": "2549",
    "name": "Shan",
    "country_id": "150"
  }, {
    "id": "2550",
    "name": "Tanintharyi",
    "country_id": "150"
  }, {
    "id": "2551",
    "name": "Yangon",
    "country_id": "150"
  }, {
    "id": "2552",
    "name": "Caprivi",
    "country_id": "151"
  }, {
    "id": "2553",
    "name": "Erongo",
    "country_id": "151"
  }, {
    "id": "2554",
    "name": "Hardap",
    "country_id": "151"
  }, {
    "id": "2555",
    "name": "Karas",
    "country_id": "151"
  }, {
    "id": "2556",
    "name": "Kavango",
    "country_id": "151"
  }, {
    "id": "2557",
    "name": "Khomas",
    "country_id": "151"
  }, {
    "id": "2558",
    "name": "Kunene",
    "country_id": "151"
  }, {
    "id": "2559",
    "name": "Ohangwena",
    "country_id": "151"
  }, {
    "id": "2560",
    "name": "Omaheke",
    "country_id": "151"
  }, {
    "id": "2561",
    "name": "Omusati",
    "country_id": "151"
  }, {
    "id": "2562",
    "name": "Oshana",
    "country_id": "151"
  }, {
    "id": "2563",
    "name": "Oshikoto",
    "country_id": "151"
  }, {
    "id": "2564",
    "name": "Otjozondjupa",
    "country_id": "151"
  }, {
    "id": "2565",
    "name": "Yaren",
    "country_id": "152"
  }, {
    "id": "2566",
    "name": "Bagmati",
    "country_id": "153"
  }, {
    "id": "2567",
    "name": "Bheri",
    "country_id": "153"
  }, {
    "id": "2568",
    "name": "Dhawalagiri",
    "country_id": "153"
  }, {
    "id": "2569",
    "name": "Gandaki",
    "country_id": "153"
  }, {
    "id": "2570",
    "name": "Janakpur",
    "country_id": "153"
  }, {
    "id": "2571",
    "name": "Karnali",
    "country_id": "153"
  }, {
    "id": "2572",
    "name": "Koshi",
    "country_id": "153"
  }, {
    "id": "2573",
    "name": "Lumbini",
    "country_id": "153"
  }, {
    "id": "2574",
    "name": "Mahakali",
    "country_id": "153"
  }, {
    "id": "2575",
    "name": "Mechi",
    "country_id": "153"
  }, {
    "id": "2576",
    "name": "Narayani",
    "country_id": "153"
  }, {
    "id": "2577",
    "name": "Rapti",
    "country_id": "153"
  }, {
    "id": "2578",
    "name": "Sagarmatha",
    "country_id": "153"
  }, {
    "id": "2579",
    "name": "Seti",
    "country_id": "153"
  }, {
    "id": "2580",
    "name": "Bonaire",
    "country_id": "154"
  }, {
    "id": "2581",
    "name": "Curacao",
    "country_id": "154"
  }, {
    "id": "2582",
    "name": "Saba",
    "country_id": "154"
  }, {
    "id": "2583",
    "name": "Sint Eustatius",
    "country_id": "154"
  }, {
    "id": "2584",
    "name": "Sint Maarten",
    "country_id": "154"
  }, {
    "id": "2585",
    "name": "Amsterdam",
    "country_id": "155"
  }, {
    "id": "2586",
    "name": "Benelux",
    "country_id": "155"
  }, {
    "id": "2587",
    "name": "Drenthe",
    "country_id": "155"
  }, {
    "id": "2588",
    "name": "Flevoland",
    "country_id": "155"
  }, {
    "id": "2589",
    "name": "Friesland",
    "country_id": "155"
  }, {
    "id": "2590",
    "name": "Gelderland",
    "country_id": "155"
  }, {
    "id": "2591",
    "name": "Groningen",
    "country_id": "155"
  }, {
    "id": "2592",
    "name": "Limburg",
    "country_id": "155"
  }, {
    "id": "2593",
    "name": "Noord-Brabant",
    "country_id": "155"
  }, {
    "id": "2594",
    "name": "Noord-Holland",
    "country_id": "155"
  }, {
    "id": "2595",
    "name": "Overijssel",
    "country_id": "155"
  }, {
    "id": "2596",
    "name": "South Holland",
    "country_id": "155"
  }, {
    "id": "2597",
    "name": "Utrecht",
    "country_id": "155"
  }, {
    "id": "2598",
    "name": "Zeeland",
    "country_id": "155"
  }, {
    "id": "2599",
    "name": "Zuid-Holland",
    "country_id": "155"
  }, {
    "id": "2600",
    "name": "Iles",
    "country_id": "156"
  }, {
    "id": "2601",
    "name": "Nord",
    "country_id": "156"
  }, {
    "id": "2602",
    "name": "Sud",
    "country_id": "156"
  }, {
    "id": "2603",
    "name": "Area Outside Region",
    "country_id": "157"
  }, {
    "id": "2604",
    "name": "Auckland",
    "country_id": "157"
  }, {
    "id": "2605",
    "name": "Bay of Plenty",
    "country_id": "157"
  }, {
    "id": "2606",
    "name": "Canterbury",
    "country_id": "157"
  }, {
    "id": "2607",
    "name": "Christchurch",
    "country_id": "157"
  }, {
    "id": "2608",
    "name": "Gisborne",
    "country_id": "157"
  }, {
    "id": "2609",
    "name": "Hawke's Bay",
    "country_id": "157"
  }, {
    "id": "2610",
    "name": "Manawatu-Wanganui",
    "country_id": "157"
  }, {
    "id": "2611",
    "name": "Marlborough",
    "country_id": "157"
  }, {
    "id": "2612",
    "name": "Nelson",
    "country_id": "157"
  }, {
    "id": "2613",
    "name": "Northland",
    "country_id": "157"
  }, {
    "id": "2614",
    "name": "Otago",
    "country_id": "157"
  }, {
    "id": "2615",
    "name": "Rodney",
    "country_id": "157"
  }, {
    "id": "2616",
    "name": "Southland",
    "country_id": "157"
  }, {
    "id": "2617",
    "name": "Taranaki",
    "country_id": "157"
  }, {
    "id": "2618",
    "name": "Tasman",
    "country_id": "157"
  }, {
    "id": "2619",
    "name": "Waikato",
    "country_id": "157"
  }, {
    "id": "2620",
    "name": "Wellington",
    "country_id": "157"
  }, {
    "id": "2621",
    "name": "West Coast",
    "country_id": "157"
  }, {
    "id": "2622",
    "name": "Atlantico Norte",
    "country_id": "158"
  }, {
    "id": "2623",
    "name": "Atlantico Sur",
    "country_id": "158"
  }, {
    "id": "2624",
    "name": "Boaco",
    "country_id": "158"
  }, {
    "id": "2625",
    "name": "Carazo",
    "country_id": "158"
  }, {
    "id": "2626",
    "name": "Chinandega",
    "country_id": "158"
  }, {
    "id": "2627",
    "name": "Chontales",
    "country_id": "158"
  }, {
    "id": "2628",
    "name": "Esteli",
    "country_id": "158"
  }, {
    "id": "2629",
    "name": "Granada",
    "country_id": "158"
  }, {
    "id": "2630",
    "name": "Jinotega",
    "country_id": "158"
  }, {
    "id": "2631",
    "name": "Leon",
    "country_id": "158"
  }, {
    "id": "2632",
    "name": "Madriz",
    "country_id": "158"
  }, {
    "id": "2633",
    "name": "Managua",
    "country_id": "158"
  }, {
    "id": "2634",
    "name": "Masaya",
    "country_id": "158"
  }, {
    "id": "2635",
    "name": "Matagalpa",
    "country_id": "158"
  }, {
    "id": "2636",
    "name": "Nueva Segovia",
    "country_id": "158"
  }, {
    "id": "2637",
    "name": "Rio San Juan",
    "country_id": "158"
  }, {
    "id": "2638",
    "name": "Rivas",
    "country_id": "158"
  }, {
    "id": "2639",
    "name": "Agadez",
    "country_id": "159"
  }, {
    "id": "2640",
    "name": "Diffa",
    "country_id": "159"
  }, {
    "id": "2641",
    "name": "Dosso",
    "country_id": "159"
  }, {
    "id": "2642",
    "name": "Maradi",
    "country_id": "159"
  }, {
    "id": "2643",
    "name": "Niamey",
    "country_id": "159"
  }, {
    "id": "2644",
    "name": "Tahoua",
    "country_id": "159"
  }, {
    "id": "2645",
    "name": "Tillabery",
    "country_id": "159"
  }, {
    "id": "2646",
    "name": "Zinder",
    "country_id": "159"
  }, {
    "id": "2647",
    "name": "Abia",
    "country_id": "160"
  }, {
    "id": "2648",
    "name": "Abuja Federal Capital Territory",
    "country_id": "160"
  }, {
    "id": "2649",
    "name": "Adamawa",
    "country_id": "160"
  }, {
    "id": "2650",
    "name": "Akwa Ibom",
    "country_id": "160"
  }, {
    "id": "2651",
    "name": "Anambra",
    "country_id": "160"
  }, {
    "id": "2652",
    "name": "Bauchi",
    "country_id": "160"
  }, {
    "id": "2653",
    "name": "Bayelsa",
    "country_id": "160"
  }, {
    "id": "2654",
    "name": "Benue",
    "country_id": "160"
  }, {
    "id": "2655",
    "name": "Borno",
    "country_id": "160"
  }, {
    "id": "2656",
    "name": "Cross River",
    "country_id": "160"
  }, {
    "id": "2657",
    "name": "Delta",
    "country_id": "160"
  }, {
    "id": "2658",
    "name": "Ebonyi",
    "country_id": "160"
  }, {
    "id": "2659",
    "name": "Edo",
    "country_id": "160"
  }, {
    "id": "2660",
    "name": "Ekiti",
    "country_id": "160"
  }, {
    "id": "2661",
    "name": "Enugu",
    "country_id": "160"
  }, {
    "id": "2662",
    "name": "Gombe",
    "country_id": "160"
  }, {
    "id": "2663",
    "name": "Imo",
    "country_id": "160"
  }, {
    "id": "2664",
    "name": "Jigawa",
    "country_id": "160"
  }, {
    "id": "2665",
    "name": "Kaduna",
    "country_id": "160"
  }, {
    "id": "2666",
    "name": "Kano",
    "country_id": "160"
  }, {
    "id": "2667",
    "name": "Katsina",
    "country_id": "160"
  }, {
    "id": "2668",
    "name": "Kebbi",
    "country_id": "160"
  }, {
    "id": "2669",
    "name": "Kogi",
    "country_id": "160"
  }, {
    "id": "2670",
    "name": "Kwara",
    "country_id": "160"
  }, {
    "id": "2671",
    "name": "Lagos",
    "country_id": "160"
  }, {
    "id": "2672",
    "name": "Nassarawa",
    "country_id": "160"
  }, {
    "id": "2673",
    "name": "Niger",
    "country_id": "160"
  }, {
    "id": "2674",
    "name": "Ogun",
    "country_id": "160"
  }, {
    "id": "2675",
    "name": "Ondo",
    "country_id": "160"
  }, {
    "id": "2676",
    "name": "Osun",
    "country_id": "160"
  }, {
    "id": "2677",
    "name": "Oyo",
    "country_id": "160"
  }, {
    "id": "2678",
    "name": "Plateau",
    "country_id": "160"
  }, {
    "id": "2679",
    "name": "Rivers",
    "country_id": "160"
  }, {
    "id": "2680",
    "name": "Sokoto",
    "country_id": "160"
  }, {
    "id": "2681",
    "name": "Taraba",
    "country_id": "160"
  }, {
    "id": "2682",
    "name": "Yobe",
    "country_id": "160"
  }, {
    "id": "2683",
    "name": "Zamfara",
    "country_id": "160"
  }, {
    "id": "2684",
    "name": "Niue",
    "country_id": "161"
  }, {
    "id": "2685",
    "name": "Norfolk Island",
    "country_id": "162"
  }, {
    "id": "2686",
    "name": "Northern Islands",
    "country_id": "163"
  }, {
    "id": "2687",
    "name": "Rota",
    "country_id": "163"
  }, {
    "id": "2688",
    "name": "Saipan",
    "country_id": "163"
  }, {
    "id": "2689",
    "name": "Tinian",
    "country_id": "163"
  }, {
    "id": "2690",
    "name": "Akershus",
    "country_id": "164"
  }, {
    "id": "2691",
    "name": "Aust Agder",
    "country_id": "164"
  }, {
    "id": "2692",
    "name": "Bergen",
    "country_id": "164"
  }, {
    "id": "2693",
    "name": "Buskerud",
    "country_id": "164"
  }, {
    "id": "2694",
    "name": "Finnmark",
    "country_id": "164"
  }, {
    "id": "2695",
    "name": "Hedmark",
    "country_id": "164"
  }, {
    "id": "2696",
    "name": "Hordaland",
    "country_id": "164"
  }, {
    "id": "2697",
    "name": "Moere og Romsdal",
    "country_id": "164"
  }, {
    "id": "2698",
    "name": "Nord Trondelag",
    "country_id": "164"
  }, {
    "id": "2699",
    "name": "Nordland",
    "country_id": "164"
  }, {
    "id": "2700",
    "name": "Oestfold",
    "country_id": "164"
  }, {
    "id": "2701",
    "name": "Oppland",
    "country_id": "164"
  }, {
    "id": "2702",
    "name": "Oslo",
    "country_id": "164"
  }, {
    "id": "2703",
    "name": "Rogaland",
    "country_id": "164"
  }, {
    "id": "2704",
    "name": "Soer Troendelag",
    "country_id": "164"
  }, {
    "id": "2705",
    "name": "Sogn og Fjordane",
    "country_id": "164"
  }, {
    "id": "2706",
    "name": "Stavern",
    "country_id": "164"
  }, {
    "id": "2707",
    "name": "Sykkylven",
    "country_id": "164"
  }, {
    "id": "2708",
    "name": "Telemark",
    "country_id": "164"
  }, {
    "id": "2709",
    "name": "Troms",
    "country_id": "164"
  }, {
    "id": "2710",
    "name": "Vest Agder",
    "country_id": "164"
  }, {
    "id": "2711",
    "name": "Vestfold",
    "country_id": "164"
  }, {
    "id": "2712",
    "name": "\xC3\u0192\xC2\u02DCstfold",
    "country_id": "164"
  }, {
    "id": "2713",
    "name": "Al Buraimi",
    "country_id": "165"
  }, {
    "id": "2714",
    "name": "Dhufar",
    "country_id": "165"
  }, {
    "id": "2715",
    "name": "Masqat",
    "country_id": "165"
  }, {
    "id": "2716",
    "name": "Musandam",
    "country_id": "165"
  }, {
    "id": "2717",
    "name": "Rusayl",
    "country_id": "165"
  }, {
    "id": "2718",
    "name": "Wadi Kabir",
    "country_id": "165"
  }, {
    "id": "2719",
    "name": "ad-Dakhiliyah",
    "country_id": "165"
  }, {
    "id": "2720",
    "name": "adh-Dhahirah",
    "country_id": "165"
  }, {
    "id": "2721",
    "name": "al-Batinah",
    "country_id": "165"
  }, {
    "id": "2722",
    "name": "ash-Sharqiyah",
    "country_id": "165"
  }, {
    "id": "2723",
    "name": "Baluchistan",
    "country_id": "166"
  }, {
    "id": "2724",
    "name": "Federal Capital Area",
    "country_id": "166"
  }, {
    "id": "2725",
    "name": "Federally administered Tribal ",
    "country_id": "166"
  }, {
    "id": "2726",
    "name": "North-West Frontier",
    "country_id": "166"
  }, {
    "id": "2727",
    "name": "Northern Areas",
    "country_id": "166"
  }, {
    "id": "2728",
    "name": "Punjab",
    "country_id": "166"
  }, {
    "id": "2729",
    "name": "Sind",
    "country_id": "166"
  }, {
    "id": "2730",
    "name": "Aimeliik",
    "country_id": "167"
  }, {
    "id": "2731",
    "name": "Airai",
    "country_id": "167"
  }, {
    "id": "2732",
    "name": "Angaur",
    "country_id": "167"
  }, {
    "id": "2733",
    "name": "Hatobohei",
    "country_id": "167"
  }, {
    "id": "2734",
    "name": "Kayangel",
    "country_id": "167"
  }, {
    "id": "2735",
    "name": "Koror",
    "country_id": "167"
  }, {
    "id": "2736",
    "name": "Melekeok",
    "country_id": "167"
  }, {
    "id": "2737",
    "name": "Ngaraard",
    "country_id": "167"
  }, {
    "id": "2738",
    "name": "Ngardmau",
    "country_id": "167"
  }, {
    "id": "2739",
    "name": "Ngaremlengui",
    "country_id": "167"
  }, {
    "id": "2740",
    "name": "Ngatpang",
    "country_id": "167"
  }, {
    "id": "2741",
    "name": "Ngchesar",
    "country_id": "167"
  }, {
    "id": "2742",
    "name": "Ngerchelong",
    "country_id": "167"
  }, {
    "id": "2743",
    "name": "Ngiwal",
    "country_id": "167"
  }, {
    "id": "2744",
    "name": "Peleliu",
    "country_id": "167"
  }, {
    "id": "2745",
    "name": "Sonsorol",
    "country_id": "167"
  }, {
    "id": "2746",
    "name": "Ariha",
    "country_id": "168"
  }, {
    "id": "2747",
    "name": "Bayt Lahm",
    "country_id": "168"
  }, {
    "id": "2748",
    "name": "Bethlehem",
    "country_id": "168"
  }, {
    "id": "2749",
    "name": "Dayr-al-Balah",
    "country_id": "168"
  }, {
    "id": "2750",
    "name": "Ghazzah",
    "country_id": "168"
  }, {
    "id": "2751",
    "name": "Ghazzah ash-Shamaliyah",
    "country_id": "168"
  }, {
    "id": "2752",
    "name": "Janin",
    "country_id": "168"
  }, {
    "id": "2753",
    "name": "Khan Yunis",
    "country_id": "168"
  }, {
    "id": "2754",
    "name": "Nabulus",
    "country_id": "168"
  }, {
    "id": "2755",
    "name": "Qalqilyah",
    "country_id": "168"
  }, {
    "id": "2756",
    "name": "Rafah",
    "country_id": "168"
  }, {
    "id": "2757",
    "name": "Ram Allah wal-Birah",
    "country_id": "168"
  }, {
    "id": "2758",
    "name": "Salfit",
    "country_id": "168"
  }, {
    "id": "2759",
    "name": "Tubas",
    "country_id": "168"
  }, {
    "id": "2760",
    "name": "Tulkarm",
    "country_id": "168"
  }, {
    "id": "2761",
    "name": "al-Khalil",
    "country_id": "168"
  }, {
    "id": "2762",
    "name": "al-Quds",
    "country_id": "168"
  }, {
    "id": "2763",
    "name": "Bocas del Toro",
    "country_id": "169"
  }, {
    "id": "2764",
    "name": "Chiriqui",
    "country_id": "169"
  }, {
    "id": "2765",
    "name": "Cocle",
    "country_id": "169"
  }, {
    "id": "2766",
    "name": "Colon",
    "country_id": "169"
  }, {
    "id": "2767",
    "name": "Darien",
    "country_id": "169"
  }, {
    "id": "2768",
    "name": "Embera",
    "country_id": "169"
  }, {
    "id": "2769",
    "name": "Herrera",
    "country_id": "169"
  }, {
    "id": "2770",
    "name": "Kuna Yala",
    "country_id": "169"
  }, {
    "id": "2771",
    "name": "Los Santos",
    "country_id": "169"
  }, {
    "id": "2772",
    "name": "Ngobe Bugle",
    "country_id": "169"
  }, {
    "id": "2773",
    "name": "Panama",
    "country_id": "169"
  }, {
    "id": "2774",
    "name": "Veraguas",
    "country_id": "169"
  }, {
    "id": "2775",
    "name": "East New Britain",
    "country_id": "170"
  }, {
    "id": "2776",
    "name": "East Sepik",
    "country_id": "170"
  }, {
    "id": "2777",
    "name": "Eastern Highlands",
    "country_id": "170"
  }, {
    "id": "2778",
    "name": "Enga",
    "country_id": "170"
  }, {
    "id": "2779",
    "name": "Fly River",
    "country_id": "170"
  }, {
    "id": "2780",
    "name": "Gulf",
    "country_id": "170"
  }, {
    "id": "2781",
    "name": "Madang",
    "country_id": "170"
  }, {
    "id": "2782",
    "name": "Manus",
    "country_id": "170"
  }, {
    "id": "2783",
    "name": "Milne Bay",
    "country_id": "170"
  }, {
    "id": "2784",
    "name": "Morobe",
    "country_id": "170"
  }, {
    "id": "2785",
    "name": "National Capital District",
    "country_id": "170"
  }, {
    "id": "2786",
    "name": "New Ireland",
    "country_id": "170"
  }, {
    "id": "2787",
    "name": "North Solomons",
    "country_id": "170"
  }, {
    "id": "2788",
    "name": "Oro",
    "country_id": "170"
  }, {
    "id": "2789",
    "name": "Sandaun",
    "country_id": "170"
  }, {
    "id": "2790",
    "name": "Simbu",
    "country_id": "170"
  }, {
    "id": "2791",
    "name": "Southern Highlands",
    "country_id": "170"
  }, {
    "id": "2792",
    "name": "West New Britain",
    "country_id": "170"
  }, {
    "id": "2793",
    "name": "Western Highlands",
    "country_id": "170"
  }, {
    "id": "2794",
    "name": "Alto Paraguay",
    "country_id": "171"
  }, {
    "id": "2795",
    "name": "Alto Parana",
    "country_id": "171"
  }, {
    "id": "2796",
    "name": "Amambay",
    "country_id": "171"
  }, {
    "id": "2797",
    "name": "Asuncion",
    "country_id": "171"
  }, {
    "id": "2798",
    "name": "Boqueron",
    "country_id": "171"
  }, {
    "id": "2799",
    "name": "Caaguazu",
    "country_id": "171"
  }, {
    "id": "2800",
    "name": "Caazapa",
    "country_id": "171"
  }, {
    "id": "2801",
    "name": "Canendiyu",
    "country_id": "171"
  }, {
    "id": "2802",
    "name": "Central",
    "country_id": "171"
  }, {
    "id": "2803",
    "name": "Concepcion",
    "country_id": "171"
  }, {
    "id": "2804",
    "name": "Cordillera",
    "country_id": "171"
  }, {
    "id": "2805",
    "name": "Guaira",
    "country_id": "171"
  }, {
    "id": "2806",
    "name": "Itapua",
    "country_id": "171"
  }, {
    "id": "2807",
    "name": "Misiones",
    "country_id": "171"
  }, {
    "id": "2808",
    "name": "Neembucu",
    "country_id": "171"
  }, {
    "id": "2809",
    "name": "Paraguari",
    "country_id": "171"
  }, {
    "id": "2810",
    "name": "Presidente Hayes",
    "country_id": "171"
  }, {
    "id": "2811",
    "name": "San Pedro",
    "country_id": "171"
  }, {
    "id": "2812",
    "name": "Amazonas",
    "country_id": "172"
  }, {
    "id": "2813",
    "name": "Ancash",
    "country_id": "172"
  }, {
    "id": "2814",
    "name": "Apurimac",
    "country_id": "172"
  }, {
    "id": "2815",
    "name": "Arequipa",
    "country_id": "172"
  }, {
    "id": "2816",
    "name": "Ayacucho",
    "country_id": "172"
  }, {
    "id": "2817",
    "name": "Cajamarca",
    "country_id": "172"
  }, {
    "id": "2818",
    "name": "Cusco",
    "country_id": "172"
  }, {
    "id": "2819",
    "name": "Huancavelica",
    "country_id": "172"
  }, {
    "id": "2820",
    "name": "Huanuco",
    "country_id": "172"
  }, {
    "id": "2821",
    "name": "Ica",
    "country_id": "172"
  }, {
    "id": "2822",
    "name": "Junin",
    "country_id": "172"
  }, {
    "id": "2823",
    "name": "La Libertad",
    "country_id": "172"
  }, {
    "id": "2824",
    "name": "Lambayeque",
    "country_id": "172"
  }, {
    "id": "2825",
    "name": "Lima y Callao",
    "country_id": "172"
  }, {
    "id": "2826",
    "name": "Loreto",
    "country_id": "172"
  }, {
    "id": "2827",
    "name": "Madre de Dios",
    "country_id": "172"
  }, {
    "id": "2828",
    "name": "Moquegua",
    "country_id": "172"
  }, {
    "id": "2829",
    "name": "Pasco",
    "country_id": "172"
  }, {
    "id": "2830",
    "name": "Piura",
    "country_id": "172"
  }, {
    "id": "2831",
    "name": "Puno",
    "country_id": "172"
  }, {
    "id": "2832",
    "name": "San Martin",
    "country_id": "172"
  }, {
    "id": "2833",
    "name": "Tacna",
    "country_id": "172"
  }, {
    "id": "2834",
    "name": "Tumbes",
    "country_id": "172"
  }, {
    "id": "2835",
    "name": "Ucayali",
    "country_id": "172"
  }, {
    "id": "2836",
    "name": "Batangas",
    "country_id": "173"
  }, {
    "id": "2837",
    "name": "Bicol",
    "country_id": "173"
  }, {
    "id": "2838",
    "name": "Bulacan",
    "country_id": "173"
  }, {
    "id": "2839",
    "name": "Cagayan",
    "country_id": "173"
  }, {
    "id": "2840",
    "name": "Caraga",
    "country_id": "173"
  }, {
    "id": "2841",
    "name": "Central Luzon",
    "country_id": "173"
  }, {
    "id": "2842",
    "name": "Central Mindanao",
    "country_id": "173"
  }, {
    "id": "2843",
    "name": "Central Visayas",
    "country_id": "173"
  }, {
    "id": "2844",
    "name": "Cordillera",
    "country_id": "173"
  }, {
    "id": "2845",
    "name": "Davao",
    "country_id": "173"
  }, {
    "id": "2846",
    "name": "Eastern Visayas",
    "country_id": "173"
  }, {
    "id": "2847",
    "name": "Greater Metropolitan Area",
    "country_id": "173"
  }, {
    "id": "2848",
    "name": "Ilocos",
    "country_id": "173"
  }, {
    "id": "2849",
    "name": "Laguna",
    "country_id": "173"
  }, {
    "id": "2850",
    "name": "Luzon",
    "country_id": "173"
  }, {
    "id": "2851",
    "name": "Mactan",
    "country_id": "173"
  }, {
    "id": "2852",
    "name": "Metropolitan Manila Area",
    "country_id": "173"
  }, {
    "id": "2853",
    "name": "Muslim Mindanao",
    "country_id": "173"
  }, {
    "id": "2854",
    "name": "Northern Mindanao",
    "country_id": "173"
  }, {
    "id": "2855",
    "name": "Southern Mindanao",
    "country_id": "173"
  }, {
    "id": "2856",
    "name": "Southern Tagalog",
    "country_id": "173"
  }, {
    "id": "2857",
    "name": "Western Mindanao",
    "country_id": "173"
  }, {
    "id": "2858",
    "name": "Western Visayas",
    "country_id": "173"
  }, {
    "id": "2859",
    "name": "Pitcairn Island",
    "country_id": "174"
  }, {
    "id": "2860",
    "name": "Biale Blota",
    "country_id": "175"
  }, {
    "id": "2861",
    "name": "Dobroszyce",
    "country_id": "175"
  }, {
    "id": "2862",
    "name": "Dolnoslaskie",
    "country_id": "175"
  }, {
    "id": "2863",
    "name": "Dziekanow Lesny",
    "country_id": "175"
  }, {
    "id": "2864",
    "name": "Hopowo",
    "country_id": "175"
  }, {
    "id": "2865",
    "name": "Kartuzy",
    "country_id": "175"
  }, {
    "id": "2866",
    "name": "Koscian",
    "country_id": "175"
  }, {
    "id": "2867",
    "name": "Krakow",
    "country_id": "175"
  }, {
    "id": "2868",
    "name": "Kujawsko-Pomorskie",
    "country_id": "175"
  }, {
    "id": "2869",
    "name": "Lodzkie",
    "country_id": "175"
  }, {
    "id": "2870",
    "name": "Lubelskie",
    "country_id": "175"
  }, {
    "id": "2871",
    "name": "Lubuskie",
    "country_id": "175"
  }, {
    "id": "2872",
    "name": "Malomice",
    "country_id": "175"
  }, {
    "id": "2873",
    "name": "Malopolskie",
    "country_id": "175"
  }, {
    "id": "2874",
    "name": "Mazowieckie",
    "country_id": "175"
  }, {
    "id": "2875",
    "name": "Mirkow",
    "country_id": "175"
  }, {
    "id": "2876",
    "name": "Opolskie",
    "country_id": "175"
  }, {
    "id": "2877",
    "name": "Ostrowiec",
    "country_id": "175"
  }, {
    "id": "2878",
    "name": "Podkarpackie",
    "country_id": "175"
  }, {
    "id": "2879",
    "name": "Podlaskie",
    "country_id": "175"
  }, {
    "id": "2880",
    "name": "Polska",
    "country_id": "175"
  }, {
    "id": "2881",
    "name": "Pomorskie",
    "country_id": "175"
  }, {
    "id": "2882",
    "name": "Poznan",
    "country_id": "175"
  }, {
    "id": "2883",
    "name": "Pruszkow",
    "country_id": "175"
  }, {
    "id": "2884",
    "name": "Rymanowska",
    "country_id": "175"
  }, {
    "id": "2885",
    "name": "Rzeszow",
    "country_id": "175"
  }, {
    "id": "2886",
    "name": "Slaskie",
    "country_id": "175"
  }, {
    "id": "2887",
    "name": "Stare Pole",
    "country_id": "175"
  }, {
    "id": "2888",
    "name": "Swietokrzyskie",
    "country_id": "175"
  }, {
    "id": "2889",
    "name": "Warminsko-Mazurskie",
    "country_id": "175"
  }, {
    "id": "2890",
    "name": "Warsaw",
    "country_id": "175"
  }, {
    "id": "2891",
    "name": "Wejherowo",
    "country_id": "175"
  }, {
    "id": "2892",
    "name": "Wielkopolskie",
    "country_id": "175"
  }, {
    "id": "2893",
    "name": "Wroclaw",
    "country_id": "175"
  }, {
    "id": "2894",
    "name": "Zachodnio-Pomorskie",
    "country_id": "175"
  }, {
    "id": "2895",
    "name": "Zukowo",
    "country_id": "175"
  }, {
    "id": "2896",
    "name": "Abrantes",
    "country_id": "176"
  }, {
    "id": "2897",
    "name": "Acores",
    "country_id": "176"
  }, {
    "id": "2898",
    "name": "Alentejo",
    "country_id": "176"
  }, {
    "id": "2899",
    "name": "Algarve",
    "country_id": "176"
  }, {
    "id": "2900",
    "name": "Braga",
    "country_id": "176"
  }, {
    "id": "2901",
    "name": "Centro",
    "country_id": "176"
  }, {
    "id": "2902",
    "name": "Distrito de Leiria",
    "country_id": "176"
  }, {
    "id": "2903",
    "name": "Distrito de Viana do Castelo",
    "country_id": "176"
  }, {
    "id": "2904",
    "name": "Distrito de Vila Real",
    "country_id": "176"
  }, {
    "id": "2905",
    "name": "Distrito do Porto",
    "country_id": "176"
  }, {
    "id": "2906",
    "name": "Lisboa e Vale do Tejo",
    "country_id": "176"
  }, {
    "id": "2907",
    "name": "Madeira",
    "country_id": "176"
  }, {
    "id": "2908",
    "name": "Norte",
    "country_id": "176"
  }, {
    "id": "2909",
    "name": "Paivas",
    "country_id": "176"
  }, {
    "id": "2910",
    "name": "Arecibo",
    "country_id": "177"
  }, {
    "id": "2911",
    "name": "Bayamon",
    "country_id": "177"
  }, {
    "id": "2912",
    "name": "Carolina",
    "country_id": "177"
  }, {
    "id": "2913",
    "name": "Florida",
    "country_id": "177"
  }, {
    "id": "2914",
    "name": "Guayama",
    "country_id": "177"
  }, {
    "id": "2915",
    "name": "Humacao",
    "country_id": "177"
  }, {
    "id": "2916",
    "name": "Mayaguez-Aguadilla",
    "country_id": "177"
  }, {
    "id": "2917",
    "name": "Ponce",
    "country_id": "177"
  }, {
    "id": "2918",
    "name": "Salinas",
    "country_id": "177"
  }, {
    "id": "2919",
    "name": "San Juan",
    "country_id": "177"
  }, {
    "id": "2920",
    "name": "Doha",
    "country_id": "178"
  }, {
    "id": "2921",
    "name": "Jarian-al-Batnah",
    "country_id": "178"
  }, {
    "id": "2922",
    "name": "Umm Salal",
    "country_id": "178"
  }, {
    "id": "2923",
    "name": "ad-Dawhah",
    "country_id": "178"
  }, {
    "id": "2924",
    "name": "al-Ghuwayriyah",
    "country_id": "178"
  }, {
    "id": "2925",
    "name": "al-Jumayliyah",
    "country_id": "178"
  }, {
    "id": "2926",
    "name": "al-Khawr",
    "country_id": "178"
  }, {
    "id": "2927",
    "name": "al-Wakrah",
    "country_id": "178"
  }, {
    "id": "2928",
    "name": "ar-Rayyan",
    "country_id": "178"
  }, {
    "id": "2929",
    "name": "ash-Shamal",
    "country_id": "178"
  }, {
    "id": "2930",
    "name": "Saint-Benoit",
    "country_id": "179"
  }, {
    "id": "2931",
    "name": "Saint-Denis",
    "country_id": "179"
  }, {
    "id": "2932",
    "name": "Saint-Paul",
    "country_id": "179"
  }, {
    "id": "2933",
    "name": "Saint-Pierre",
    "country_id": "179"
  }, {
    "id": "2934",
    "name": "Alba",
    "country_id": "180"
  }, {
    "id": "2935",
    "name": "Arad",
    "country_id": "180"
  }, {
    "id": "2936",
    "name": "Arges",
    "country_id": "180"
  }, {
    "id": "2937",
    "name": "Bacau",
    "country_id": "180"
  }, {
    "id": "2938",
    "name": "Bihor",
    "country_id": "180"
  }, {
    "id": "2939",
    "name": "Bistrita-Nasaud",
    "country_id": "180"
  }, {
    "id": "2940",
    "name": "Botosani",
    "country_id": "180"
  }, {
    "id": "2941",
    "name": "Braila",
    "country_id": "180"
  }, {
    "id": "2942",
    "name": "Brasov",
    "country_id": "180"
  }, {
    "id": "2943",
    "name": "Bucuresti",
    "country_id": "180"
  }, {
    "id": "2944",
    "name": "Buzau",
    "country_id": "180"
  }, {
    "id": "2945",
    "name": "Calarasi",
    "country_id": "180"
  }, {
    "id": "2946",
    "name": "Caras-Severin",
    "country_id": "180"
  }, {
    "id": "2947",
    "name": "Cluj",
    "country_id": "180"
  }, {
    "id": "2948",
    "name": "Constanta",
    "country_id": "180"
  }, {
    "id": "2949",
    "name": "Covasna",
    "country_id": "180"
  }, {
    "id": "2950",
    "name": "Dambovita",
    "country_id": "180"
  }, {
    "id": "2951",
    "name": "Dolj",
    "country_id": "180"
  }, {
    "id": "2952",
    "name": "Galati",
    "country_id": "180"
  }, {
    "id": "2953",
    "name": "Giurgiu",
    "country_id": "180"
  }, {
    "id": "2954",
    "name": "Gorj",
    "country_id": "180"
  }, {
    "id": "2955",
    "name": "Harghita",
    "country_id": "180"
  }, {
    "id": "2956",
    "name": "Hunedoara",
    "country_id": "180"
  }, {
    "id": "2957",
    "name": "Ialomita",
    "country_id": "180"
  }, {
    "id": "2958",
    "name": "Iasi",
    "country_id": "180"
  }, {
    "id": "2959",
    "name": "Ilfov",
    "country_id": "180"
  }, {
    "id": "2960",
    "name": "Maramures",
    "country_id": "180"
  }, {
    "id": "2961",
    "name": "Mehedinti",
    "country_id": "180"
  }, {
    "id": "2962",
    "name": "Mures",
    "country_id": "180"
  }, {
    "id": "2963",
    "name": "Neamt",
    "country_id": "180"
  }, {
    "id": "2964",
    "name": "Olt",
    "country_id": "180"
  }, {
    "id": "2965",
    "name": "Prahova",
    "country_id": "180"
  }, {
    "id": "2966",
    "name": "Salaj",
    "country_id": "180"
  }, {
    "id": "2967",
    "name": "Satu Mare",
    "country_id": "180"
  }, {
    "id": "2968",
    "name": "Sibiu",
    "country_id": "180"
  }, {
    "id": "2969",
    "name": "Sondelor",
    "country_id": "180"
  }, {
    "id": "2970",
    "name": "Suceava",
    "country_id": "180"
  }, {
    "id": "2971",
    "name": "Teleorman",
    "country_id": "180"
  }, {
    "id": "2972",
    "name": "Timis",
    "country_id": "180"
  }, {
    "id": "2973",
    "name": "Tulcea",
    "country_id": "180"
  }, {
    "id": "2974",
    "name": "Valcea",
    "country_id": "180"
  }, {
    "id": "2975",
    "name": "Vaslui",
    "country_id": "180"
  }, {
    "id": "2976",
    "name": "Vrancea",
    "country_id": "180"
  }, {
    "id": "2977",
    "name": "Adygeja",
    "country_id": "181"
  }, {
    "id": "2978",
    "name": "Aga",
    "country_id": "181"
  }, {
    "id": "2979",
    "name": "Alanija",
    "country_id": "181"
  }, {
    "id": "2980",
    "name": "Altaj",
    "country_id": "181"
  }, {
    "id": "2981",
    "name": "Amur",
    "country_id": "181"
  }, {
    "id": "2982",
    "name": "Arhangelsk",
    "country_id": "181"
  }, {
    "id": "2983",
    "name": "Astrahan",
    "country_id": "181"
  }, {
    "id": "2984",
    "name": "Bashkortostan",
    "country_id": "181"
  }, {
    "id": "2985",
    "name": "Belgorod",
    "country_id": "181"
  }, {
    "id": "2986",
    "name": "Brjansk",
    "country_id": "181"
  }, {
    "id": "2987",
    "name": "Burjatija",
    "country_id": "181"
  }, {
    "id": "2988",
    "name": "Chechenija",
    "country_id": "181"
  }, {
    "id": "2989",
    "name": "Cheljabinsk",
    "country_id": "181"
  }, {
    "id": "2990",
    "name": "Chita",
    "country_id": "181"
  }, {
    "id": "2991",
    "name": "Chukotka",
    "country_id": "181"
  }, {
    "id": "2992",
    "name": "Chuvashija",
    "country_id": "181"
  }, {
    "id": "2993",
    "name": "Dagestan",
    "country_id": "181"
  }, {
    "id": "2994",
    "name": "Evenkija",
    "country_id": "181"
  }, {
    "id": "2995",
    "name": "Gorno-Altaj",
    "country_id": "181"
  }, {
    "id": "2996",
    "name": "Habarovsk",
    "country_id": "181"
  }, {
    "id": "2997",
    "name": "Hakasija",
    "country_id": "181"
  }, {
    "id": "2998",
    "name": "Hanty-Mansija",
    "country_id": "181"
  }, {
    "id": "2999",
    "name": "Ingusetija",
    "country_id": "181"
  }, {
    "id": "3000",
    "name": "Irkutsk",
    "country_id": "181"
  }, {
    "id": "3001",
    "name": "Ivanovo",
    "country_id": "181"
  }, {
    "id": "3002",
    "name": "Jamalo-Nenets",
    "country_id": "181"
  }, {
    "id": "3003",
    "name": "Jaroslavl",
    "country_id": "181"
  }, {
    "id": "3004",
    "name": "Jevrej",
    "country_id": "181"
  }, {
    "id": "3005",
    "name": "Kabardino-Balkarija",
    "country_id": "181"
  }, {
    "id": "3006",
    "name": "Kaliningrad",
    "country_id": "181"
  }, {
    "id": "3007",
    "name": "Kalmykija",
    "country_id": "181"
  }, {
    "id": "3008",
    "name": "Kaluga",
    "country_id": "181"
  }, {
    "id": "3009",
    "name": "Kamchatka",
    "country_id": "181"
  }, {
    "id": "3010",
    "name": "Karachaj-Cherkessija",
    "country_id": "181"
  }, {
    "id": "3011",
    "name": "Karelija",
    "country_id": "181"
  }, {
    "id": "3012",
    "name": "Kemerovo",
    "country_id": "181"
  }, {
    "id": "3013",
    "name": "Khabarovskiy Kray",
    "country_id": "181"
  }, {
    "id": "3014",
    "name": "Kirov",
    "country_id": "181"
  }, {
    "id": "3015",
    "name": "Komi",
    "country_id": "181"
  }, {
    "id": "3016",
    "name": "Komi-Permjakija",
    "country_id": "181"
  }, {
    "id": "3017",
    "name": "Korjakija",
    "country_id": "181"
  }, {
    "id": "3018",
    "name": "Kostroma",
    "country_id": "181"
  }, {
    "id": "3019",
    "name": "Krasnodar",
    "country_id": "181"
  }, {
    "id": "3020",
    "name": "Krasnojarsk",
    "country_id": "181"
  }, {
    "id": "3021",
    "name": "Krasnoyarskiy Kray",
    "country_id": "181"
  }, {
    "id": "3022",
    "name": "Kurgan",
    "country_id": "181"
  }, {
    "id": "3023",
    "name": "Kursk",
    "country_id": "181"
  }, {
    "id": "3024",
    "name": "Leningrad",
    "country_id": "181"
  }, {
    "id": "3025",
    "name": "Lipeck",
    "country_id": "181"
  }, {
    "id": "3026",
    "name": "Magadan",
    "country_id": "181"
  }, {
    "id": "3027",
    "name": "Marij El",
    "country_id": "181"
  }, {
    "id": "3028",
    "name": "Mordovija",
    "country_id": "181"
  }, {
    "id": "3029",
    "name": "Moscow",
    "country_id": "181"
  }, {
    "id": "3030",
    "name": "Moskovskaja Oblast",
    "country_id": "181"
  }, {
    "id": "3031",
    "name": "Moskovskaya Oblast",
    "country_id": "181"
  }, {
    "id": "3032",
    "name": "Moskva",
    "country_id": "181"
  }, {
    "id": "3033",
    "name": "Murmansk",
    "country_id": "181"
  }, {
    "id": "3034",
    "name": "Nenets",
    "country_id": "181"
  }, {
    "id": "3035",
    "name": "Nizhnij Novgorod",
    "country_id": "181"
  }, {
    "id": "3036",
    "name": "Novgorod",
    "country_id": "181"
  }, {
    "id": "3037",
    "name": "Novokusnezk",
    "country_id": "181"
  }, {
    "id": "3038",
    "name": "Novosibirsk",
    "country_id": "181"
  }, {
    "id": "3039",
    "name": "Omsk",
    "country_id": "181"
  }, {
    "id": "3040",
    "name": "Orenburg",
    "country_id": "181"
  }, {
    "id": "3041",
    "name": "Orjol",
    "country_id": "181"
  }, {
    "id": "3042",
    "name": "Penza",
    "country_id": "181"
  }, {
    "id": "3043",
    "name": "Perm",
    "country_id": "181"
  }, {
    "id": "3044",
    "name": "Primorje",
    "country_id": "181"
  }, {
    "id": "3045",
    "name": "Pskov",
    "country_id": "181"
  }, {
    "id": "3046",
    "name": "Pskovskaya Oblast",
    "country_id": "181"
  }, {
    "id": "3047",
    "name": "Rjazan",
    "country_id": "181"
  }, {
    "id": "3048",
    "name": "Rostov",
    "country_id": "181"
  }, {
    "id": "3049",
    "name": "Saha",
    "country_id": "181"
  }, {
    "id": "3050",
    "name": "Sahalin",
    "country_id": "181"
  }, {
    "id": "3051",
    "name": "Samara",
    "country_id": "181"
  }, {
    "id": "3052",
    "name": "Samarskaya",
    "country_id": "181"
  }, {
    "id": "3053",
    "name": "Sankt-Peterburg",
    "country_id": "181"
  }, {
    "id": "3054",
    "name": "Saratov",
    "country_id": "181"
  }, {
    "id": "3055",
    "name": "Smolensk",
    "country_id": "181"
  }, {
    "id": "3056",
    "name": "Stavropol",
    "country_id": "181"
  }, {
    "id": "3057",
    "name": "Sverdlovsk",
    "country_id": "181"
  }, {
    "id": "3058",
    "name": "Tajmyrija",
    "country_id": "181"
  }, {
    "id": "3059",
    "name": "Tambov",
    "country_id": "181"
  }, {
    "id": "3060",
    "name": "Tatarstan",
    "country_id": "181"
  }, {
    "id": "3061",
    "name": "Tjumen",
    "country_id": "181"
  }, {
    "id": "3062",
    "name": "Tomsk",
    "country_id": "181"
  }, {
    "id": "3063",
    "name": "Tula",
    "country_id": "181"
  }, {
    "id": "3064",
    "name": "Tver",
    "country_id": "181"
  }, {
    "id": "3065",
    "name": "Tyva",
    "country_id": "181"
  }, {
    "id": "3066",
    "name": "Udmurtija",
    "country_id": "181"
  }, {
    "id": "3067",
    "name": "Uljanovsk",
    "country_id": "181"
  }, {
    "id": "3068",
    "name": "Ulyanovskaya Oblast",
    "country_id": "181"
  }, {
    "id": "3069",
    "name": "Ust-Orda",
    "country_id": "181"
  }, {
    "id": "3070",
    "name": "Vladimir",
    "country_id": "181"
  }, {
    "id": "3071",
    "name": "Volgograd",
    "country_id": "181"
  }, {
    "id": "3072",
    "name": "Vologda",
    "country_id": "181"
  }, {
    "id": "3073",
    "name": "Voronezh",
    "country_id": "181"
  }, {
    "id": "3074",
    "name": "Butare",
    "country_id": "182"
  }, {
    "id": "3075",
    "name": "Byumba",
    "country_id": "182"
  }, {
    "id": "3076",
    "name": "Cyangugu",
    "country_id": "182"
  }, {
    "id": "3077",
    "name": "Gikongoro",
    "country_id": "182"
  }, {
    "id": "3078",
    "name": "Gisenyi",
    "country_id": "182"
  }, {
    "id": "3079",
    "name": "Gitarama",
    "country_id": "182"
  }, {
    "id": "3080",
    "name": "Kibungo",
    "country_id": "182"
  }, {
    "id": "3081",
    "name": "Kibuye",
    "country_id": "182"
  }, {
    "id": "3082",
    "name": "Kigali-ngali",
    "country_id": "182"
  }, {
    "id": "3083",
    "name": "Ruhengeri",
    "country_id": "182"
  }, {
    "id": "3084",
    "name": "Ascension",
    "country_id": "183"
  }, {
    "id": "3085",
    "name": "Gough Island",
    "country_id": "183"
  }, {
    "id": "3086",
    "name": "Saint Helena",
    "country_id": "183"
  }, {
    "id": "3087",
    "name": "Tristan da Cunha",
    "country_id": "183"
  }, {
    "id": "3088",
    "name": "Christ Church Nichola Town",
    "country_id": "184"
  }, {
    "id": "3089",
    "name": "Saint Anne Sandy Point",
    "country_id": "184"
  }, {
    "id": "3090",
    "name": "Saint George Basseterre",
    "country_id": "184"
  }, {
    "id": "3091",
    "name": "Saint George Gingerland",
    "country_id": "184"
  }, {
    "id": "3092",
    "name": "Saint James Windward",
    "country_id": "184"
  }, {
    "id": "3093",
    "name": "Saint John Capesterre",
    "country_id": "184"
  }, {
    "id": "3094",
    "name": "Saint John Figtree",
    "country_id": "184"
  }, {
    "id": "3095",
    "name": "Saint Mary Cayon",
    "country_id": "184"
  }, {
    "id": "3096",
    "name": "Saint Paul Capesterre",
    "country_id": "184"
  }, {
    "id": "3097",
    "name": "Saint Paul Charlestown",
    "country_id": "184"
  }, {
    "id": "3098",
    "name": "Saint Peter Basseterre",
    "country_id": "184"
  }, {
    "id": "3099",
    "name": "Saint Thomas Lowland",
    "country_id": "184"
  }, {
    "id": "3100",
    "name": "Saint Thomas Middle Island",
    "country_id": "184"
  }, {
    "id": "3101",
    "name": "Trinity Palmetto Point",
    "country_id": "184"
  }, {
    "id": "3102",
    "name": "Anse-la-Raye",
    "country_id": "185"
  }, {
    "id": "3103",
    "name": "Canaries",
    "country_id": "185"
  }, {
    "id": "3104",
    "name": "Castries",
    "country_id": "185"
  }, {
    "id": "3105",
    "name": "Choiseul",
    "country_id": "185"
  }, {
    "id": "3106",
    "name": "Dennery",
    "country_id": "185"
  }, {
    "id": "3107",
    "name": "Gros Inlet",
    "country_id": "185"
  }, {
    "id": "3108",
    "name": "Laborie",
    "country_id": "185"
  }, {
    "id": "3109",
    "name": "Micoud",
    "country_id": "185"
  }, {
    "id": "3110",
    "name": "Soufriere",
    "country_id": "185"
  }, {
    "id": "3111",
    "name": "Vieux Fort",
    "country_id": "185"
  }, {
    "id": "3112",
    "name": "Miquelon-Langlade",
    "country_id": "186"
  }, {
    "id": "3113",
    "name": "Saint-Pierre",
    "country_id": "186"
  }, {
    "id": "3114",
    "name": "Charlotte",
    "country_id": "187"
  }, {
    "id": "3115",
    "name": "Grenadines",
    "country_id": "187"
  }, {
    "id": "3116",
    "name": "Saint Andrew",
    "country_id": "187"
  }, {
    "id": "3117",
    "name": "Saint David",
    "country_id": "187"
  }, {
    "id": "3118",
    "name": "Saint George",
    "country_id": "187"
  }, {
    "id": "3119",
    "name": "Saint Patrick",
    "country_id": "187"
  }, {
    "id": "3120",
    "name": "A'ana",
    "country_id": "188"
  }, {
    "id": "3121",
    "name": "Aiga-i-le-Tai",
    "country_id": "188"
  }, {
    "id": "3122",
    "name": "Atua",
    "country_id": "188"
  }, {
    "id": "3123",
    "name": "Fa'asaleleaga",
    "country_id": "188"
  }, {
    "id": "3124",
    "name": "Gaga'emauga",
    "country_id": "188"
  }, {
    "id": "3125",
    "name": "Gagaifomauga",
    "country_id": "188"
  }, {
    "id": "3126",
    "name": "Palauli",
    "country_id": "188"
  }, {
    "id": "3127",
    "name": "Satupa'itea",
    "country_id": "188"
  }, {
    "id": "3128",
    "name": "Tuamasaga",
    "country_id": "188"
  }, {
    "id": "3129",
    "name": "Va'a-o-Fonoti",
    "country_id": "188"
  }, {
    "id": "3130",
    "name": "Vaisigano",
    "country_id": "188"
  }, {
    "id": "3131",
    "name": "Acquaviva",
    "country_id": "189"
  }, {
    "id": "3132",
    "name": "Borgo Maggiore",
    "country_id": "189"
  }, {
    "id": "3133",
    "name": "Chiesanuova",
    "country_id": "189"
  }, {
    "id": "3134",
    "name": "Domagnano",
    "country_id": "189"
  }, {
    "id": "3135",
    "name": "Faetano",
    "country_id": "189"
  }, {
    "id": "3136",
    "name": "Fiorentino",
    "country_id": "189"
  }, {
    "id": "3137",
    "name": "Montegiardino",
    "country_id": "189"
  }, {
    "id": "3138",
    "name": "San Marino",
    "country_id": "189"
  }, {
    "id": "3139",
    "name": "Serravalle",
    "country_id": "189"
  }, {
    "id": "3140",
    "name": "Agua Grande",
    "country_id": "190"
  }, {
    "id": "3141",
    "name": "Cantagalo",
    "country_id": "190"
  }, {
    "id": "3142",
    "name": "Lemba",
    "country_id": "190"
  }, {
    "id": "3143",
    "name": "Lobata",
    "country_id": "190"
  }, {
    "id": "3144",
    "name": "Me-Zochi",
    "country_id": "190"
  }, {
    "id": "3145",
    "name": "Pague",
    "country_id": "190"
  }, {
    "id": "3146",
    "name": "Al Khobar",
    "country_id": "191"
  }, {
    "id": "3147",
    "name": "Aseer",
    "country_id": "191"
  }, {
    "id": "3148",
    "name": "Ash Sharqiyah",
    "country_id": "191"
  }, {
    "id": "3149",
    "name": "Asir",
    "country_id": "191"
  }, {
    "id": "3150",
    "name": "Central Province",
    "country_id": "191"
  }, {
    "id": "3151",
    "name": "Eastern Province",
    "country_id": "191"
  }, {
    "id": "3152",
    "name": "Ha'il",
    "country_id": "191"
  }, {
    "id": "3153",
    "name": "Jawf",
    "country_id": "191"
  }, {
    "id": "3154",
    "name": "Jizan",
    "country_id": "191"
  }, {
    "id": "3155",
    "name": "Makkah",
    "country_id": "191"
  }, {
    "id": "3156",
    "name": "Najran",
    "country_id": "191"
  }, {
    "id": "3157",
    "name": "Qasim",
    "country_id": "191"
  }, {
    "id": "3158",
    "name": "Tabuk",
    "country_id": "191"
  }, {
    "id": "3159",
    "name": "Western Province",
    "country_id": "191"
  }, {
    "id": "3160",
    "name": "al-Bahah",
    "country_id": "191"
  }, {
    "id": "3161",
    "name": "al-Hudud-ash-Shamaliyah",
    "country_id": "191"
  }, {
    "id": "3162",
    "name": "al-Madinah",
    "country_id": "191"
  }, {
    "id": "3163",
    "name": "ar-Riyad",
    "country_id": "191"
  }, {
    "id": "3164",
    "name": "Dakar",
    "country_id": "192"
  }, {
    "id": "3165",
    "name": "Diourbel",
    "country_id": "192"
  }, {
    "id": "3166",
    "name": "Fatick",
    "country_id": "192"
  }, {
    "id": "3167",
    "name": "Kaolack",
    "country_id": "192"
  }, {
    "id": "3168",
    "name": "Kolda",
    "country_id": "192"
  }, {
    "id": "3169",
    "name": "Louga",
    "country_id": "192"
  }, {
    "id": "3170",
    "name": "Saint-Louis",
    "country_id": "192"
  }, {
    "id": "3171",
    "name": "Tambacounda",
    "country_id": "192"
  }, {
    "id": "3172",
    "name": "Thies",
    "country_id": "192"
  }, {
    "id": "3173",
    "name": "Ziguinchor",
    "country_id": "192"
  }, {
    "id": "3174",
    "name": "Central Serbia",
    "country_id": "193"
  }, {
    "id": "3175",
    "name": "Kosovo and Metohija",
    "country_id": "193"
  }, {
    "id": "3176",
    "name": "Vojvodina",
    "country_id": "193"
  }, {
    "id": "3177",
    "name": "Anse Boileau",
    "country_id": "194"
  }, {
    "id": "3178",
    "name": "Anse Royale",
    "country_id": "194"
  }, {
    "id": "3179",
    "name": "Cascade",
    "country_id": "194"
  }, {
    "id": "3180",
    "name": "Takamaka",
    "country_id": "194"
  }, {
    "id": "3181",
    "name": "Victoria",
    "country_id": "194"
  }, {
    "id": "3182",
    "name": "Eastern",
    "country_id": "195"
  }, {
    "id": "3183",
    "name": "Northern",
    "country_id": "195"
  }, {
    "id": "3184",
    "name": "Southern",
    "country_id": "195"
  }, {
    "id": "3185",
    "name": "Western",
    "country_id": "195"
  }, {
    "id": "3186",
    "name": "Singapore",
    "country_id": "196"
  }, {
    "id": "3187",
    "name": "Banskobystricky",
    "country_id": "197"
  }, {
    "id": "3188",
    "name": "Bratislavsky",
    "country_id": "197"
  }, {
    "id": "3189",
    "name": "Kosicky",
    "country_id": "197"
  }, {
    "id": "3190",
    "name": "Nitriansky",
    "country_id": "197"
  }, {
    "id": "3191",
    "name": "Presovsky",
    "country_id": "197"
  }, {
    "id": "3192",
    "name": "Trenciansky",
    "country_id": "197"
  }, {
    "id": "3193",
    "name": "Trnavsky",
    "country_id": "197"
  }, {
    "id": "3194",
    "name": "Zilinsky",
    "country_id": "197"
  }, {
    "id": "3195",
    "name": "Benedikt",
    "country_id": "198"
  }, {
    "id": "3196",
    "name": "Gorenjska",
    "country_id": "198"
  }, {
    "id": "3197",
    "name": "Gorishka",
    "country_id": "198"
  }, {
    "id": "3198",
    "name": "Jugovzhodna Slovenija",
    "country_id": "198"
  }, {
    "id": "3199",
    "name": "Koroshka",
    "country_id": "198"
  }, {
    "id": "3200",
    "name": "Notranjsko-krashka",
    "country_id": "198"
  }, {
    "id": "3201",
    "name": "Obalno-krashka",
    "country_id": "198"
  }, {
    "id": "3202",
    "name": "Obcina Domzale",
    "country_id": "198"
  }, {
    "id": "3203",
    "name": "Obcina Vitanje",
    "country_id": "198"
  }, {
    "id": "3204",
    "name": "Osrednjeslovenska",
    "country_id": "198"
  }, {
    "id": "3205",
    "name": "Podravska",
    "country_id": "198"
  }, {
    "id": "3206",
    "name": "Pomurska",
    "country_id": "198"
  }, {
    "id": "3207",
    "name": "Savinjska",
    "country_id": "198"
  }, {
    "id": "3208",
    "name": "Slovenian Littoral",
    "country_id": "198"
  }, {
    "id": "3209",
    "name": "Spodnjeposavska",
    "country_id": "198"
  }, {
    "id": "3210",
    "name": "Zasavska",
    "country_id": "198"
  }, {
    "id": "3211",
    "name": "Pitcairn",
    "country_id": "199"
  }, {
    "id": "3212",
    "name": "Central",
    "country_id": "200"
  }, {
    "id": "3213",
    "name": "Choiseul",
    "country_id": "200"
  }, {
    "id": "3214",
    "name": "Guadalcanal",
    "country_id": "200"
  }, {
    "id": "3215",
    "name": "Isabel",
    "country_id": "200"
  }, {
    "id": "3216",
    "name": "Makira and Ulawa",
    "country_id": "200"
  }, {
    "id": "3217",
    "name": "Malaita",
    "country_id": "200"
  }, {
    "id": "3218",
    "name": "Rennell and Bellona",
    "country_id": "200"
  }, {
    "id": "3219",
    "name": "Temotu",
    "country_id": "200"
  }, {
    "id": "3220",
    "name": "Western",
    "country_id": "200"
  }, {
    "id": "3221",
    "name": "Awdal",
    "country_id": "201"
  }, {
    "id": "3222",
    "name": "Bakol",
    "country_id": "201"
  }, {
    "id": "3223",
    "name": "Banadir",
    "country_id": "201"
  }, {
    "id": "3224",
    "name": "Bari",
    "country_id": "201"
  }, {
    "id": "3225",
    "name": "Bay",
    "country_id": "201"
  }, {
    "id": "3226",
    "name": "Galgudug",
    "country_id": "201"
  }, {
    "id": "3227",
    "name": "Gedo",
    "country_id": "201"
  }, {
    "id": "3228",
    "name": "Hiran",
    "country_id": "201"
  }, {
    "id": "3229",
    "name": "Jubbada Hose",
    "country_id": "201"
  }, {
    "id": "3230",
    "name": "Jubbadha Dexe",
    "country_id": "201"
  }, {
    "id": "3231",
    "name": "Mudug",
    "country_id": "201"
  }, {
    "id": "3232",
    "name": "Nugal",
    "country_id": "201"
  }, {
    "id": "3233",
    "name": "Sanag",
    "country_id": "201"
  }, {
    "id": "3234",
    "name": "Shabellaha Dhexe",
    "country_id": "201"
  }, {
    "id": "3235",
    "name": "Shabellaha Hose",
    "country_id": "201"
  }, {
    "id": "3236",
    "name": "Togdher",
    "country_id": "201"
  }, {
    "id": "3237",
    "name": "Woqoyi Galbed",
    "country_id": "201"
  }, {
    "id": "3238",
    "name": "Eastern Cape",
    "country_id": "202"
  }, {
    "id": "3239",
    "name": "Free State",
    "country_id": "202"
  }, {
    "id": "3240",
    "name": "Gauteng",
    "country_id": "202"
  }, {
    "id": "3241",
    "name": "Kempton Park",
    "country_id": "202"
  }, {
    "id": "3242",
    "name": "Kramerville",
    "country_id": "202"
  }, {
    "id": "3243",
    "name": "KwaZulu Natal",
    "country_id": "202"
  }, {
    "id": "3244",
    "name": "Limpopo",
    "country_id": "202"
  }, {
    "id": "3245",
    "name": "Mpumalanga",
    "country_id": "202"
  }, {
    "id": "3246",
    "name": "North West",
    "country_id": "202"
  }, {
    "id": "3247",
    "name": "Northern Cape",
    "country_id": "202"
  }, {
    "id": "3248",
    "name": "Parow",
    "country_id": "202"
  }, {
    "id": "3249",
    "name": "Table View",
    "country_id": "202"
  }, {
    "id": "3250",
    "name": "Umtentweni",
    "country_id": "202"
  }, {
    "id": "3251",
    "name": "Western Cape",
    "country_id": "202"
  }, {
    "id": "3252",
    "name": "South Georgia",
    "country_id": "203"
  }, {
    "id": "3253",
    "name": "Central Equatoria",
    "country_id": "204"
  }, {
    "id": "3254",
    "name": "A Coruna",
    "country_id": "205"
  }, {
    "id": "3255",
    "name": "Alacant",
    "country_id": "205"
  }, {
    "id": "3256",
    "name": "Alava",
    "country_id": "205"
  }, {
    "id": "3257",
    "name": "Albacete",
    "country_id": "205"
  }, {
    "id": "3258",
    "name": "Almeria",
    "country_id": "205"
  }, {
    "id": "3260",
    "name": "Asturias",
    "country_id": "205"
  }, {
    "id": "3261",
    "name": "Avila",
    "country_id": "205"
  }, {
    "id": "3262",
    "name": "Badajoz",
    "country_id": "205"
  }, {
    "id": "3263",
    "name": "Balears",
    "country_id": "205"
  }, {
    "id": "3264",
    "name": "Barcelona",
    "country_id": "205"
  }, {
    "id": "3267",
    "name": "Burgos",
    "country_id": "205"
  }, {
    "id": "3268",
    "name": "Caceres",
    "country_id": "205"
  }, {
    "id": "3269",
    "name": "Cadiz",
    "country_id": "205"
  }, {
    "id": "3270",
    "name": "Cantabria",
    "country_id": "205"
  }, {
    "id": "3271",
    "name": "Castello",
    "country_id": "205"
  }, {
    "id": "3273",
    "name": "Ceuta",
    "country_id": "205"
  }, {
    "id": "3274",
    "name": "Ciudad Real",
    "country_id": "205"
  }, {
    "id": "3281",
    "name": "Cordoba",
    "country_id": "205"
  }, {
    "id": "3282",
    "name": "Cuenca",
    "country_id": "205"
  }, {
    "id": "3284",
    "name": "Girona",
    "country_id": "205"
  }, {
    "id": "3285",
    "name": "Granada",
    "country_id": "205"
  }, {
    "id": "3286",
    "name": "Guadalajara",
    "country_id": "205"
  }, {
    "id": "3287",
    "name": "Guipuzcoa",
    "country_id": "205"
  }, {
    "id": "3288",
    "name": "Huelva",
    "country_id": "205"
  }, {
    "id": "3289",
    "name": "Huesca",
    "country_id": "205"
  }, {
    "id": "3290",
    "name": "Jaen",
    "country_id": "205"
  }, {
    "id": "3291",
    "name": "La Rioja",
    "country_id": "205"
  }, {
    "id": "3292",
    "name": "Las Palmas",
    "country_id": "205"
  }, {
    "id": "3293",
    "name": "Leon",
    "country_id": "205"
  }, {
    "id": "3295",
    "name": "Lleida",
    "country_id": "205"
  }, {
    "id": "3296",
    "name": "Lugo",
    "country_id": "205"
  }, {
    "id": "3297",
    "name": "Madrid",
    "country_id": "205"
  }, {
    "id": "3298",
    "name": "Malaga",
    "country_id": "205"
  }, {
    "id": "3299",
    "name": "Melilla",
    "country_id": "205"
  }, {
    "id": "3300",
    "name": "Murcia",
    "country_id": "205"
  }, {
    "id": "3301",
    "name": "Navarra",
    "country_id": "205"
  }, {
    "id": "3302",
    "name": "Ourense",
    "country_id": "205"
  }, {
    "id": "3303",
    "name": "Pais Vasco",
    "country_id": "205"
  }, {
    "id": "3304",
    "name": "Palencia",
    "country_id": "205"
  }, {
    "id": "3305",
    "name": "Pontevedra",
    "country_id": "205"
  }, {
    "id": "3306",
    "name": "Salamanca",
    "country_id": "205"
  }, {
    "id": "3308",
    "name": "Segovia",
    "country_id": "205"
  }, {
    "id": "3309",
    "name": "Sevilla",
    "country_id": "205"
  }, {
    "id": "3310",
    "name": "Soria",
    "country_id": "205"
  }, {
    "id": "3311",
    "name": "Tarragona",
    "country_id": "205"
  }, {
    "id": "3312",
    "name": "Santa Cruz de Tenerife",
    "country_id": "205"
  }, {
    "id": "3313",
    "name": "Teruel",
    "country_id": "205"
  }, {
    "id": "3314",
    "name": "Toledo",
    "country_id": "205"
  }, {
    "id": "3315",
    "name": "Valencia",
    "country_id": "205"
  }, {
    "id": "3316",
    "name": "Valladolid",
    "country_id": "205"
  }, {
    "id": "3317",
    "name": "Vizcaya",
    "country_id": "205"
  }, {
    "id": "3318",
    "name": "Zamora",
    "country_id": "205"
  }, {
    "id": "3319",
    "name": "Zaragoza",
    "country_id": "205"
  }, {
    "id": "3320",
    "name": "Amparai",
    "country_id": "206"
  }, {
    "id": "3321",
    "name": "Anuradhapuraya",
    "country_id": "206"
  }, {
    "id": "3322",
    "name": "Badulla",
    "country_id": "206"
  }, {
    "id": "3323",
    "name": "Boralesgamuwa",
    "country_id": "206"
  }, {
    "id": "3324",
    "name": "Colombo",
    "country_id": "206"
  }, {
    "id": "3325",
    "name": "Galla",
    "country_id": "206"
  }, {
    "id": "3326",
    "name": "Gampaha",
    "country_id": "206"
  }, {
    "id": "3327",
    "name": "Hambantota",
    "country_id": "206"
  }, {
    "id": "3328",
    "name": "Kalatura",
    "country_id": "206"
  }, {
    "id": "3329",
    "name": "Kegalla",
    "country_id": "206"
  }, {
    "id": "3330",
    "name": "Kilinochchi",
    "country_id": "206"
  }, {
    "id": "3331",
    "name": "Kurunegala",
    "country_id": "206"
  }, {
    "id": "3332",
    "name": "Madakalpuwa",
    "country_id": "206"
  }, {
    "id": "3333",
    "name": "Maha Nuwara",
    "country_id": "206"
  }, {
    "id": "3334",
    "name": "Malwana",
    "country_id": "206"
  }, {
    "id": "3335",
    "name": "Mannarama",
    "country_id": "206"
  }, {
    "id": "3336",
    "name": "Matale",
    "country_id": "206"
  }, {
    "id": "3337",
    "name": "Matara",
    "country_id": "206"
  }, {
    "id": "3338",
    "name": "Monaragala",
    "country_id": "206"
  }, {
    "id": "3339",
    "name": "Mullaitivu",
    "country_id": "206"
  }, {
    "id": "3340",
    "name": "North Eastern Province",
    "country_id": "206"
  }, {
    "id": "3341",
    "name": "North Western Province",
    "country_id": "206"
  }, {
    "id": "3342",
    "name": "Nuwara Eliya",
    "country_id": "206"
  }, {
    "id": "3343",
    "name": "Polonnaruwa",
    "country_id": "206"
  }, {
    "id": "3344",
    "name": "Puttalama",
    "country_id": "206"
  }, {
    "id": "3345",
    "name": "Ratnapuraya",
    "country_id": "206"
  }, {
    "id": "3346",
    "name": "Southern Province",
    "country_id": "206"
  }, {
    "id": "3347",
    "name": "Tirikunamalaya",
    "country_id": "206"
  }, {
    "id": "3348",
    "name": "Tuscany",
    "country_id": "206"
  }, {
    "id": "3349",
    "name": "Vavuniyawa",
    "country_id": "206"
  }, {
    "id": "3350",
    "name": "Western Province",
    "country_id": "206"
  }, {
    "id": "3351",
    "name": "Yapanaya",
    "country_id": "206"
  }, {
    "id": "3352",
    "name": "kadawatha",
    "country_id": "206"
  }, {
    "id": "3353",
    "name": "A'ali-an-Nil",
    "country_id": "207"
  }, {
    "id": "3354",
    "name": "Bahr-al-Jabal",
    "country_id": "207"
  }, {
    "id": "3355",
    "name": "Central Equatoria",
    "country_id": "207"
  }, {
    "id": "3356",
    "name": "Gharb Bahr-al-Ghazal",
    "country_id": "207"
  }, {
    "id": "3357",
    "name": "Gharb Darfur",
    "country_id": "207"
  }, {
    "id": "3358",
    "name": "Gharb Kurdufan",
    "country_id": "207"
  }, {
    "id": "3359",
    "name": "Gharb-al-Istiwa'iyah",
    "country_id": "207"
  }, {
    "id": "3360",
    "name": "Janub Darfur",
    "country_id": "207"
  }, {
    "id": "3361",
    "name": "Janub Kurdufan",
    "country_id": "207"
  }, {
    "id": "3362",
    "name": "Junqali",
    "country_id": "207"
  }, {
    "id": "3363",
    "name": "Kassala",
    "country_id": "207"
  }, {
    "id": "3364",
    "name": "Nahr-an-Nil",
    "country_id": "207"
  }, {
    "id": "3365",
    "name": "Shamal Bahr-al-Ghazal",
    "country_id": "207"
  }, {
    "id": "3366",
    "name": "Shamal Darfur",
    "country_id": "207"
  }, {
    "id": "3367",
    "name": "Shamal Kurdufan",
    "country_id": "207"
  }, {
    "id": "3368",
    "name": "Sharq-al-Istiwa'iyah",
    "country_id": "207"
  }, {
    "id": "3369",
    "name": "Sinnar",
    "country_id": "207"
  }, {
    "id": "3370",
    "name": "Warab",
    "country_id": "207"
  }, {
    "id": "3371",
    "name": "Wilayat al Khartum",
    "country_id": "207"
  }, {
    "id": "3372",
    "name": "al-Bahr-al-Ahmar",
    "country_id": "207"
  }, {
    "id": "3373",
    "name": "al-Buhayrat",
    "country_id": "207"
  }, {
    "id": "3374",
    "name": "al-Jazirah",
    "country_id": "207"
  }, {
    "id": "3375",
    "name": "al-Khartum",
    "country_id": "207"
  }, {
    "id": "3376",
    "name": "al-Qadarif",
    "country_id": "207"
  }, {
    "id": "3377",
    "name": "al-Wahdah",
    "country_id": "207"
  }, {
    "id": "3378",
    "name": "an-Nil-al-Abyad",
    "country_id": "207"
  }, {
    "id": "3379",
    "name": "an-Nil-al-Azraq",
    "country_id": "207"
  }, {
    "id": "3380",
    "name": "ash-Shamaliyah",
    "country_id": "207"
  }, {
    "id": "3381",
    "name": "Brokopondo",
    "country_id": "208"
  }, {
    "id": "3382",
    "name": "Commewijne",
    "country_id": "208"
  }, {
    "id": "3383",
    "name": "Coronie",
    "country_id": "208"
  }, {
    "id": "3384",
    "name": "Marowijne",
    "country_id": "208"
  }, {
    "id": "3385",
    "name": "Nickerie",
    "country_id": "208"
  }, {
    "id": "3386",
    "name": "Para",
    "country_id": "208"
  }, {
    "id": "3387",
    "name": "Paramaribo",
    "country_id": "208"
  }, {
    "id": "3388",
    "name": "Saramacca",
    "country_id": "208"
  }, {
    "id": "3389",
    "name": "Wanica",
    "country_id": "208"
  }, {
    "id": "3390",
    "name": "Svalbard",
    "country_id": "209"
  }, {
    "id": "3391",
    "name": "Hhohho",
    "country_id": "210"
  }, {
    "id": "3392",
    "name": "Lubombo",
    "country_id": "210"
  }, {
    "id": "3393",
    "name": "Manzini",
    "country_id": "210"
  }, {
    "id": "3394",
    "name": "Shiselweni",
    "country_id": "210"
  }, {
    "id": "3395",
    "name": "Alvsborgs Lan",
    "country_id": "211"
  }, {
    "id": "3396",
    "name": "Angermanland",
    "country_id": "211"
  }, {
    "id": "3397",
    "name": "Blekinge",
    "country_id": "211"
  }, {
    "id": "3398",
    "name": "Bohuslan",
    "country_id": "211"
  }, {
    "id": "3399",
    "name": "Dalarna",
    "country_id": "211"
  }, {
    "id": "3400",
    "name": "Gavleborg",
    "country_id": "211"
  }, {
    "id": "3401",
    "name": "Gaza",
    "country_id": "211"
  }, {
    "id": "3402",
    "name": "Gotland",
    "country_id": "211"
  }, {
    "id": "3403",
    "name": "Halland",
    "country_id": "211"
  }, {
    "id": "3404",
    "name": "Jamtland",
    "country_id": "211"
  }, {
    "id": "3405",
    "name": "Jonkoping",
    "country_id": "211"
  }, {
    "id": "3406",
    "name": "Kalmar",
    "country_id": "211"
  }, {
    "id": "3407",
    "name": "Kristianstads",
    "country_id": "211"
  }, {
    "id": "3408",
    "name": "Kronoberg",
    "country_id": "211"
  }, {
    "id": "3409",
    "name": "Norrbotten",
    "country_id": "211"
  }, {
    "id": "3410",
    "name": "Orebro",
    "country_id": "211"
  }, {
    "id": "3411",
    "name": "Ostergotland",
    "country_id": "211"
  }, {
    "id": "3412",
    "name": "Saltsjo-Boo",
    "country_id": "211"
  }, {
    "id": "3413",
    "name": "Skane",
    "country_id": "211"
  }, {
    "id": "3414",
    "name": "Smaland",
    "country_id": "211"
  }, {
    "id": "3415",
    "name": "Sodermanland",
    "country_id": "211"
  }, {
    "id": "3416",
    "name": "Stockholm",
    "country_id": "211"
  }, {
    "id": "3417",
    "name": "Uppsala",
    "country_id": "211"
  }, {
    "id": "3418",
    "name": "Varmland",
    "country_id": "211"
  }, {
    "id": "3419",
    "name": "Vasterbotten",
    "country_id": "211"
  }, {
    "id": "3420",
    "name": "Vastergotland",
    "country_id": "211"
  }, {
    "id": "3421",
    "name": "Vasternorrland",
    "country_id": "211"
  }, {
    "id": "3422",
    "name": "Vastmanland",
    "country_id": "211"
  }, {
    "id": "3423",
    "name": "Vastra Gotaland",
    "country_id": "211"
  }, {
    "id": "3424",
    "name": "Aargau",
    "country_id": "212"
  }, {
    "id": "3425",
    "name": "Appenzell Inner-Rhoden",
    "country_id": "212"
  }, {
    "id": "3426",
    "name": "Appenzell-Ausser Rhoden",
    "country_id": "212"
  }, {
    "id": "3427",
    "name": "Basel-Landschaft",
    "country_id": "212"
  }, {
    "id": "3428",
    "name": "Basel-Stadt",
    "country_id": "212"
  }, {
    "id": "3429",
    "name": "Bern",
    "country_id": "212"
  }, {
    "id": "3430",
    "name": "Canton Ticino",
    "country_id": "212"
  }, {
    "id": "3431",
    "name": "Fribourg",
    "country_id": "212"
  }, {
    "id": "3432",
    "name": "Geneve",
    "country_id": "212"
  }, {
    "id": "3433",
    "name": "Glarus",
    "country_id": "212"
  }, {
    "id": "3434",
    "name": "Graubunden",
    "country_id": "212"
  }, {
    "id": "3435",
    "name": "Heerbrugg",
    "country_id": "212"
  }, {
    "id": "3436",
    "name": "Jura",
    "country_id": "212"
  }, {
    "id": "3437",
    "name": "Kanton Aargau",
    "country_id": "212"
  }, {
    "id": "3438",
    "name": "Luzern",
    "country_id": "212"
  }, {
    "id": "3439",
    "name": "Morbio Inferiore",
    "country_id": "212"
  }, {
    "id": "3440",
    "name": "Muhen",
    "country_id": "212"
  }, {
    "id": "3441",
    "name": "Neuchatel",
    "country_id": "212"
  }, {
    "id": "3442",
    "name": "Nidwalden",
    "country_id": "212"
  }, {
    "id": "3443",
    "name": "Obwalden",
    "country_id": "212"
  }, {
    "id": "3444",
    "name": "Sankt Gallen",
    "country_id": "212"
  }, {
    "id": "3445",
    "name": "Schaffhausen",
    "country_id": "212"
  }, {
    "id": "3446",
    "name": "Schwyz",
    "country_id": "212"
  }, {
    "id": "3447",
    "name": "Solothurn",
    "country_id": "212"
  }, {
    "id": "3448",
    "name": "Thurgau",
    "country_id": "212"
  }, {
    "id": "3449",
    "name": "Ticino",
    "country_id": "212"
  }, {
    "id": "3450",
    "name": "Uri",
    "country_id": "212"
  }, {
    "id": "3451",
    "name": "Valais",
    "country_id": "212"
  }, {
    "id": "3452",
    "name": "Vaud",
    "country_id": "212"
  }, {
    "id": "3453",
    "name": "Vauffelin",
    "country_id": "212"
  }, {
    "id": "3454",
    "name": "Zug",
    "country_id": "212"
  }, {
    "id": "3455",
    "name": "Zurich",
    "country_id": "212"
  }, {
    "id": "3456",
    "name": "Aleppo",
    "country_id": "213"
  }, {
    "id": "3457",
    "name": "Dar'a",
    "country_id": "213"
  }, {
    "id": "3458",
    "name": "Dayr-az-Zawr",
    "country_id": "213"
  }, {
    "id": "3459",
    "name": "Dimashq",
    "country_id": "213"
  }, {
    "id": "3460",
    "name": "Halab",
    "country_id": "213"
  }, {
    "id": "3461",
    "name": "Hamah",
    "country_id": "213"
  }, {
    "id": "3462",
    "name": "Hims",
    "country_id": "213"
  }, {
    "id": "3463",
    "name": "Idlib",
    "country_id": "213"
  }, {
    "id": "3464",
    "name": "Madinat Dimashq",
    "country_id": "213"
  }, {
    "id": "3465",
    "name": "Tartus",
    "country_id": "213"
  }, {
    "id": "3466",
    "name": "al-Hasakah",
    "country_id": "213"
  }, {
    "id": "3467",
    "name": "al-Ladhiqiyah",
    "country_id": "213"
  }, {
    "id": "3468",
    "name": "al-Qunaytirah",
    "country_id": "213"
  }, {
    "id": "3469",
    "name": "ar-Raqqah",
    "country_id": "213"
  }, {
    "id": "3470",
    "name": "as-Suwayda",
    "country_id": "213"
  }, {
    "id": "3471",
    "name": "Changhua County",
    "country_id": "214"
  }, {
    "id": "3472",
    "name": "Chiayi County",
    "country_id": "214"
  }, {
    "id": "3473",
    "name": "Chiayi City",
    "country_id": "214"
  }, {
    "id": "3474",
    "name": "Taipei City",
    "country_id": "214"
  }, {
    "id": "3475",
    "name": "Hsinchu County",
    "country_id": "214"
  }, {
    "id": "3476",
    "name": "Hsinchu City",
    "country_id": "214"
  }, {
    "id": "3477",
    "name": "Hualien County",
    "country_id": "214"
  }, {
    "id": "3480",
    "name": "Kaohsiung City",
    "country_id": "214"
  }, {
    "id": "3481",
    "name": "Keelung City",
    "country_id": "214"
  }, {
    "id": "3482",
    "name": "Kinmen County",
    "country_id": "214"
  }, {
    "id": "3483",
    "name": "Miaoli County",
    "country_id": "214"
  }, {
    "id": "3484",
    "name": "Nantou County",
    "country_id": "214"
  }, {
    "id": "3486",
    "name": "Penghu County",
    "country_id": "214"
  }, {
    "id": "3487",
    "name": "Pingtung County",
    "country_id": "214"
  }, {
    "id": "3488",
    "name": "Taichung City",
    "country_id": "214"
  }, {
    "id": "3492",
    "name": "Tainan City",
    "country_id": "214"
  }, {
    "id": "3493",
    "name": "New Taipei City",
    "country_id": "214"
  }, {
    "id": "3495",
    "name": "Taitung County",
    "country_id": "214"
  }, {
    "id": "3496",
    "name": "Taoyuan City",
    "country_id": "214"
  }, {
    "id": "3497",
    "name": "Yilan County",
    "country_id": "214"
  }, {
    "id": "3498",
    "name": "YunLin County",
    "country_id": "214"
  }, {
    "id": "3500",
    "name": "Dushanbe",
    "country_id": "215"
  }, {
    "id": "3501",
    "name": "Gorno-Badakhshan",
    "country_id": "215"
  }, {
    "id": "3502",
    "name": "Karotegin",
    "country_id": "215"
  }, {
    "id": "3503",
    "name": "Khatlon",
    "country_id": "215"
  }, {
    "id": "3504",
    "name": "Sughd",
    "country_id": "215"
  }, {
    "id": "3505",
    "name": "Arusha",
    "country_id": "216"
  }, {
    "id": "3506",
    "name": "Dar es Salaam",
    "country_id": "216"
  }, {
    "id": "3507",
    "name": "Dodoma",
    "country_id": "216"
  }, {
    "id": "3508",
    "name": "Iringa",
    "country_id": "216"
  }, {
    "id": "3509",
    "name": "Kagera",
    "country_id": "216"
  }, {
    "id": "3510",
    "name": "Kigoma",
    "country_id": "216"
  }, {
    "id": "3511",
    "name": "Kilimanjaro",
    "country_id": "216"
  }, {
    "id": "3512",
    "name": "Lindi",
    "country_id": "216"
  }, {
    "id": "3513",
    "name": "Mara",
    "country_id": "216"
  }, {
    "id": "3514",
    "name": "Mbeya",
    "country_id": "216"
  }, {
    "id": "3515",
    "name": "Morogoro",
    "country_id": "216"
  }, {
    "id": "3516",
    "name": "Mtwara",
    "country_id": "216"
  }, {
    "id": "3517",
    "name": "Mwanza",
    "country_id": "216"
  }, {
    "id": "3518",
    "name": "Pwani",
    "country_id": "216"
  }, {
    "id": "3519",
    "name": "Rukwa",
    "country_id": "216"
  }, {
    "id": "3520",
    "name": "Ruvuma",
    "country_id": "216"
  }, {
    "id": "3521",
    "name": "Shinyanga",
    "country_id": "216"
  }, {
    "id": "3522",
    "name": "Singida",
    "country_id": "216"
  }, {
    "id": "3523",
    "name": "Tabora",
    "country_id": "216"
  }, {
    "id": "3524",
    "name": "Tanga",
    "country_id": "216"
  }, {
    "id": "3525",
    "name": "Zanzibar and Pemba",
    "country_id": "216"
  }, {
    "id": "3526",
    "name": "Amnat Charoen",
    "country_id": "217"
  }, {
    "id": "3527",
    "name": "Ang Thong",
    "country_id": "217"
  }, {
    "id": "3528",
    "name": "Bangkok",
    "country_id": "217"
  }, {
    "id": "3529",
    "name": "Buri Ram",
    "country_id": "217"
  }, {
    "id": "3530",
    "name": "Chachoengsao",
    "country_id": "217"
  }, {
    "id": "3531",
    "name": "Chai Nat",
    "country_id": "217"
  }, {
    "id": "3532",
    "name": "Chaiyaphum",
    "country_id": "217"
  }, {
    "id": "3533",
    "name": "Changwat Chaiyaphum",
    "country_id": "217"
  }, {
    "id": "3534",
    "name": "Chanthaburi",
    "country_id": "217"
  }, {
    "id": "3535",
    "name": "Chiang Mai",
    "country_id": "217"
  }, {
    "id": "3536",
    "name": "Chiang Rai",
    "country_id": "217"
  }, {
    "id": "3537",
    "name": "Chon Buri",
    "country_id": "217"
  }, {
    "id": "3538",
    "name": "Chumphon",
    "country_id": "217"
  }, {
    "id": "3539",
    "name": "Kalasin",
    "country_id": "217"
  }, {
    "id": "3540",
    "name": "Kamphaeng Phet",
    "country_id": "217"
  }, {
    "id": "3541",
    "name": "Kanchanaburi",
    "country_id": "217"
  }, {
    "id": "3542",
    "name": "Khon Kaen",
    "country_id": "217"
  }, {
    "id": "3543",
    "name": "Krabi",
    "country_id": "217"
  }, {
    "id": "3544",
    "name": "Krung Thep",
    "country_id": "217"
  }, {
    "id": "3545",
    "name": "Lampang",
    "country_id": "217"
  }, {
    "id": "3546",
    "name": "Lamphun",
    "country_id": "217"
  }, {
    "id": "3547",
    "name": "Loei",
    "country_id": "217"
  }, {
    "id": "3548",
    "name": "Lop Buri",
    "country_id": "217"
  }, {
    "id": "3549",
    "name": "Mae Hong Son",
    "country_id": "217"
  }, {
    "id": "3550",
    "name": "Maha Sarakham",
    "country_id": "217"
  }, {
    "id": "3551",
    "name": "Mukdahan",
    "country_id": "217"
  }, {
    "id": "3552",
    "name": "Nakhon Nayok",
    "country_id": "217"
  }, {
    "id": "3553",
    "name": "Nakhon Pathom",
    "country_id": "217"
  }, {
    "id": "3554",
    "name": "Nakhon Phanom",
    "country_id": "217"
  }, {
    "id": "3555",
    "name": "Nakhon Ratchasima",
    "country_id": "217"
  }, {
    "id": "3556",
    "name": "Nakhon Sawan",
    "country_id": "217"
  }, {
    "id": "3557",
    "name": "Nakhon Si Thammarat",
    "country_id": "217"
  }, {
    "id": "3558",
    "name": "Nan",
    "country_id": "217"
  }, {
    "id": "3559",
    "name": "Narathiwat",
    "country_id": "217"
  }, {
    "id": "3560",
    "name": "Nong Bua Lam Phu",
    "country_id": "217"
  }, {
    "id": "3561",
    "name": "Nong Khai",
    "country_id": "217"
  }, {
    "id": "3562",
    "name": "Nonthaburi",
    "country_id": "217"
  }, {
    "id": "3563",
    "name": "Pathum Thani",
    "country_id": "217"
  }, {
    "id": "3564",
    "name": "Pattani",
    "country_id": "217"
  }, {
    "id": "3565",
    "name": "Phangnga",
    "country_id": "217"
  }, {
    "id": "3566",
    "name": "Phatthalung",
    "country_id": "217"
  }, {
    "id": "3567",
    "name": "Phayao",
    "country_id": "217"
  }, {
    "id": "3568",
    "name": "Phetchabun",
    "country_id": "217"
  }, {
    "id": "3569",
    "name": "Phetchaburi",
    "country_id": "217"
  }, {
    "id": "3570",
    "name": "Phichit",
    "country_id": "217"
  }, {
    "id": "3571",
    "name": "Phitsanulok",
    "country_id": "217"
  }, {
    "id": "3572",
    "name": "Phra Nakhon Si Ayutthaya",
    "country_id": "217"
  }, {
    "id": "3573",
    "name": "Phrae",
    "country_id": "217"
  }, {
    "id": "3574",
    "name": "Phuket",
    "country_id": "217"
  }, {
    "id": "3575",
    "name": "Prachin Buri",
    "country_id": "217"
  }, {
    "id": "3576",
    "name": "Prachuap Khiri Khan",
    "country_id": "217"
  }, {
    "id": "3577",
    "name": "Ranong",
    "country_id": "217"
  }, {
    "id": "3578",
    "name": "Ratchaburi",
    "country_id": "217"
  }, {
    "id": "3579",
    "name": "Rayong",
    "country_id": "217"
  }, {
    "id": "3580",
    "name": "Roi Et",
    "country_id": "217"
  }, {
    "id": "3581",
    "name": "Sa Kaeo",
    "country_id": "217"
  }, {
    "id": "3582",
    "name": "Sakon Nakhon",
    "country_id": "217"
  }, {
    "id": "3583",
    "name": "Samut Prakan",
    "country_id": "217"
  }, {
    "id": "3584",
    "name": "Samut Sakhon",
    "country_id": "217"
  }, {
    "id": "3585",
    "name": "Samut Songkhran",
    "country_id": "217"
  }, {
    "id": "3586",
    "name": "Saraburi",
    "country_id": "217"
  }, {
    "id": "3587",
    "name": "Satun",
    "country_id": "217"
  }, {
    "id": "3588",
    "name": "Si Sa Ket",
    "country_id": "217"
  }, {
    "id": "3589",
    "name": "Sing Buri",
    "country_id": "217"
  }, {
    "id": "3590",
    "name": "Songkhla",
    "country_id": "217"
  }, {
    "id": "3591",
    "name": "Sukhothai",
    "country_id": "217"
  }, {
    "id": "3592",
    "name": "Suphan Buri",
    "country_id": "217"
  }, {
    "id": "3593",
    "name": "Surat Thani",
    "country_id": "217"
  }, {
    "id": "3594",
    "name": "Surin",
    "country_id": "217"
  }, {
    "id": "3595",
    "name": "Tak",
    "country_id": "217"
  }, {
    "id": "3596",
    "name": "Trang",
    "country_id": "217"
  }, {
    "id": "3597",
    "name": "Trat",
    "country_id": "217"
  }, {
    "id": "3598",
    "name": "Ubon Ratchathani",
    "country_id": "217"
  }, {
    "id": "3599",
    "name": "Udon Thani",
    "country_id": "217"
  }, {
    "id": "3600",
    "name": "Uthai Thani",
    "country_id": "217"
  }, {
    "id": "3601",
    "name": "Uttaradit",
    "country_id": "217"
  }, {
    "id": "3602",
    "name": "Yala",
    "country_id": "217"
  }, {
    "id": "3603",
    "name": "Yasothon",
    "country_id": "217"
  }, {
    "id": "3604",
    "name": "Centre",
    "country_id": "218"
  }, {
    "id": "3605",
    "name": "Kara",
    "country_id": "218"
  }, {
    "id": "3606",
    "name": "Maritime",
    "country_id": "218"
  }, {
    "id": "3607",
    "name": "Plateaux",
    "country_id": "218"
  }, {
    "id": "3608",
    "name": "Savanes",
    "country_id": "218"
  }, {
    "id": "3609",
    "name": "Atafu",
    "country_id": "219"
  }, {
    "id": "3610",
    "name": "Fakaofo",
    "country_id": "219"
  }, {
    "id": "3611",
    "name": "Nukunonu",
    "country_id": "219"
  }, {
    "id": "3612",
    "name": "Eua",
    "country_id": "220"
  }, {
    "id": "3613",
    "name": "Ha'apai",
    "country_id": "220"
  }, {
    "id": "3614",
    "name": "Niuas",
    "country_id": "220"
  }, {
    "id": "3615",
    "name": "Tongatapu",
    "country_id": "220"
  }, {
    "id": "3616",
    "name": "Vava'u",
    "country_id": "220"
  }, {
    "id": "3617",
    "name": "Arima-Tunapuna-Piarco",
    "country_id": "221"
  }, {
    "id": "3618",
    "name": "Caroni",
    "country_id": "221"
  }, {
    "id": "3619",
    "name": "Chaguanas",
    "country_id": "221"
  }, {
    "id": "3620",
    "name": "Couva-Tabaquite-Talparo",
    "country_id": "221"
  }, {
    "id": "3621",
    "name": "Diego Martin",
    "country_id": "221"
  }, {
    "id": "3622",
    "name": "Glencoe",
    "country_id": "221"
  }, {
    "id": "3623",
    "name": "Penal Debe",
    "country_id": "221"
  }, {
    "id": "3624",
    "name": "Point Fortin",
    "country_id": "221"
  }, {
    "id": "3625",
    "name": "Port of Spain",
    "country_id": "221"
  }, {
    "id": "3626",
    "name": "Princes Town",
    "country_id": "221"
  }, {
    "id": "3627",
    "name": "Saint George",
    "country_id": "221"
  }, {
    "id": "3628",
    "name": "San Fernando",
    "country_id": "221"
  }, {
    "id": "3629",
    "name": "San Juan",
    "country_id": "221"
  }, {
    "id": "3630",
    "name": "Sangre Grande",
    "country_id": "221"
  }, {
    "id": "3631",
    "name": "Siparia",
    "country_id": "221"
  }, {
    "id": "3632",
    "name": "Tobago",
    "country_id": "221"
  }, {
    "id": "3633",
    "name": "Aryanah",
    "country_id": "222"
  }, {
    "id": "3634",
    "name": "Bajah",
    "country_id": "222"
  }, {
    "id": "3635",
    "name": "Bin 'Arus",
    "country_id": "222"
  }, {
    "id": "3636",
    "name": "Binzart",
    "country_id": "222"
  }, {
    "id": "3637",
    "name": "Gouvernorat de Ariana",
    "country_id": "222"
  }, {
    "id": "3638",
    "name": "Gouvernorat de Nabeul",
    "country_id": "222"
  }, {
    "id": "3639",
    "name": "Gouvernorat de Sousse",
    "country_id": "222"
  }, {
    "id": "3640",
    "name": "Hammamet Yasmine",
    "country_id": "222"
  }, {
    "id": "3641",
    "name": "Jundubah",
    "country_id": "222"
  }, {
    "id": "3642",
    "name": "Madaniyin",
    "country_id": "222"
  }, {
    "id": "3643",
    "name": "Manubah",
    "country_id": "222"
  }, {
    "id": "3644",
    "name": "Monastir",
    "country_id": "222"
  }, {
    "id": "3645",
    "name": "Nabul",
    "country_id": "222"
  }, {
    "id": "3646",
    "name": "Qabis",
    "country_id": "222"
  }, {
    "id": "3647",
    "name": "Qafsah",
    "country_id": "222"
  }, {
    "id": "3648",
    "name": "Qibili",
    "country_id": "222"
  }, {
    "id": "3649",
    "name": "Safaqis",
    "country_id": "222"
  }, {
    "id": "3650",
    "name": "Sfax",
    "country_id": "222"
  }, {
    "id": "3651",
    "name": "Sidi Bu Zayd",
    "country_id": "222"
  }, {
    "id": "3652",
    "name": "Silyanah",
    "country_id": "222"
  }, {
    "id": "3653",
    "name": "Susah",
    "country_id": "222"
  }, {
    "id": "3654",
    "name": "Tatawin",
    "country_id": "222"
  }, {
    "id": "3655",
    "name": "Tawzar",
    "country_id": "222"
  }, {
    "id": "3656",
    "name": "Tunis",
    "country_id": "222"
  }, {
    "id": "3657",
    "name": "Zaghwan",
    "country_id": "222"
  }, {
    "id": "3658",
    "name": "al-Kaf",
    "country_id": "222"
  }, {
    "id": "3659",
    "name": "al-Mahdiyah",
    "country_id": "222"
  }, {
    "id": "3660",
    "name": "al-Munastir",
    "country_id": "222"
  }, {
    "id": "3661",
    "name": "al-Qasrayn",
    "country_id": "222"
  }, {
    "id": "3662",
    "name": "al-Qayrawan",
    "country_id": "222"
  }, {
    "id": "3663",
    "name": "Adana",
    "country_id": "223"
  }, {
    "id": "3664",
    "name": "Adiyaman",
    "country_id": "223"
  }, {
    "id": "3665",
    "name": "Afyon",
    "country_id": "223"
  }, {
    "id": "3666",
    "name": "Agri",
    "country_id": "223"
  }, {
    "id": "3667",
    "name": "Aksaray",
    "country_id": "223"
  }, {
    "id": "3668",
    "name": "Amasya",
    "country_id": "223"
  }, {
    "id": "3669",
    "name": "Ankara",
    "country_id": "223"
  }, {
    "id": "3670",
    "name": "Antalya",
    "country_id": "223"
  }, {
    "id": "3671",
    "name": "Ardahan",
    "country_id": "223"
  }, {
    "id": "3672",
    "name": "Artvin",
    "country_id": "223"
  }, {
    "id": "3673",
    "name": "Aydin",
    "country_id": "223"
  }, {
    "id": "3674",
    "name": "Balikesir",
    "country_id": "223"
  }, {
    "id": "3675",
    "name": "Bartin",
    "country_id": "223"
  }, {
    "id": "3676",
    "name": "Batman",
    "country_id": "223"
  }, {
    "id": "3677",
    "name": "Bayburt",
    "country_id": "223"
  }, {
    "id": "3678",
    "name": "Bilecik",
    "country_id": "223"
  }, {
    "id": "3679",
    "name": "Bingol",
    "country_id": "223"
  }, {
    "id": "3680",
    "name": "Bitlis",
    "country_id": "223"
  }, {
    "id": "3681",
    "name": "Bolu",
    "country_id": "223"
  }, {
    "id": "3682",
    "name": "Burdur",
    "country_id": "223"
  }, {
    "id": "3683",
    "name": "Bursa",
    "country_id": "223"
  }, {
    "id": "3684",
    "name": "Canakkale",
    "country_id": "223"
  }, {
    "id": "3685",
    "name": "Cankiri",
    "country_id": "223"
  }, {
    "id": "3686",
    "name": "Corum",
    "country_id": "223"
  }, {
    "id": "3687",
    "name": "Denizli",
    "country_id": "223"
  }, {
    "id": "3688",
    "name": "Diyarbakir",
    "country_id": "223"
  }, {
    "id": "3689",
    "name": "Duzce",
    "country_id": "223"
  }, {
    "id": "3690",
    "name": "Edirne",
    "country_id": "223"
  }, {
    "id": "3691",
    "name": "Elazig",
    "country_id": "223"
  }, {
    "id": "3692",
    "name": "Erzincan",
    "country_id": "223"
  }, {
    "id": "3693",
    "name": "Erzurum",
    "country_id": "223"
  }, {
    "id": "3694",
    "name": "Eskisehir",
    "country_id": "223"
  }, {
    "id": "3695",
    "name": "Gaziantep",
    "country_id": "223"
  }, {
    "id": "3696",
    "name": "Giresun",
    "country_id": "223"
  }, {
    "id": "3697",
    "name": "Gumushane",
    "country_id": "223"
  }, {
    "id": "3698",
    "name": "Hakkari",
    "country_id": "223"
  }, {
    "id": "3699",
    "name": "Hatay",
    "country_id": "223"
  }, {
    "id": "3700",
    "name": "Icel",
    "country_id": "223"
  }, {
    "id": "3701",
    "name": "Igdir",
    "country_id": "223"
  }, {
    "id": "3702",
    "name": "Isparta",
    "country_id": "223"
  }, {
    "id": "3703",
    "name": "Istanbul",
    "country_id": "223"
  }, {
    "id": "3704",
    "name": "Izmir",
    "country_id": "223"
  }, {
    "id": "3705",
    "name": "Kahramanmaras",
    "country_id": "223"
  }, {
    "id": "3706",
    "name": "Karabuk",
    "country_id": "223"
  }, {
    "id": "3707",
    "name": "Karaman",
    "country_id": "223"
  }, {
    "id": "3708",
    "name": "Kars",
    "country_id": "223"
  }, {
    "id": "3709",
    "name": "Karsiyaka",
    "country_id": "223"
  }, {
    "id": "3710",
    "name": "Kastamonu",
    "country_id": "223"
  }, {
    "id": "3711",
    "name": "Kayseri",
    "country_id": "223"
  }, {
    "id": "3712",
    "name": "Kilis",
    "country_id": "223"
  }, {
    "id": "3713",
    "name": "Kirikkale",
    "country_id": "223"
  }, {
    "id": "3714",
    "name": "Kirklareli",
    "country_id": "223"
  }, {
    "id": "3715",
    "name": "Kirsehir",
    "country_id": "223"
  }, {
    "id": "3716",
    "name": "Kocaeli",
    "country_id": "223"
  }, {
    "id": "3717",
    "name": "Konya",
    "country_id": "223"
  }, {
    "id": "3718",
    "name": "Kutahya",
    "country_id": "223"
  }, {
    "id": "3719",
    "name": "Lefkosa",
    "country_id": "223"
  }, {
    "id": "3720",
    "name": "Malatya",
    "country_id": "223"
  }, {
    "id": "3721",
    "name": "Manisa",
    "country_id": "223"
  }, {
    "id": "3722",
    "name": "Mardin",
    "country_id": "223"
  }, {
    "id": "3723",
    "name": "Mugla",
    "country_id": "223"
  }, {
    "id": "3724",
    "name": "Mus",
    "country_id": "223"
  }, {
    "id": "3725",
    "name": "Nevsehir",
    "country_id": "223"
  }, {
    "id": "3726",
    "name": "Nigde",
    "country_id": "223"
  }, {
    "id": "3727",
    "name": "Ordu",
    "country_id": "223"
  }, {
    "id": "3728",
    "name": "Osmaniye",
    "country_id": "223"
  }, {
    "id": "3729",
    "name": "Rize",
    "country_id": "223"
  }, {
    "id": "3730",
    "name": "Sakarya",
    "country_id": "223"
  }, {
    "id": "3731",
    "name": "Samsun",
    "country_id": "223"
  }, {
    "id": "3732",
    "name": "Sanliurfa",
    "country_id": "223"
  }, {
    "id": "3733",
    "name": "Siirt",
    "country_id": "223"
  }, {
    "id": "3734",
    "name": "Sinop",
    "country_id": "223"
  }, {
    "id": "3735",
    "name": "Sirnak",
    "country_id": "223"
  }, {
    "id": "3736",
    "name": "Sivas",
    "country_id": "223"
  }, {
    "id": "3737",
    "name": "Tekirdag",
    "country_id": "223"
  }, {
    "id": "3738",
    "name": "Tokat",
    "country_id": "223"
  }, {
    "id": "3739",
    "name": "Trabzon",
    "country_id": "223"
  }, {
    "id": "3740",
    "name": "Tunceli",
    "country_id": "223"
  }, {
    "id": "3741",
    "name": "Usak",
    "country_id": "223"
  }, {
    "id": "3742",
    "name": "Van",
    "country_id": "223"
  }, {
    "id": "3743",
    "name": "Yalova",
    "country_id": "223"
  }, {
    "id": "3744",
    "name": "Yozgat",
    "country_id": "223"
  }, {
    "id": "3745",
    "name": "Zonguldak",
    "country_id": "223"
  }, {
    "id": "3746",
    "name": "Ahal",
    "country_id": "224"
  }, {
    "id": "3747",
    "name": "Asgabat",
    "country_id": "224"
  }, {
    "id": "3748",
    "name": "Balkan",
    "country_id": "224"
  }, {
    "id": "3749",
    "name": "Dasoguz",
    "country_id": "224"
  }, {
    "id": "3750",
    "name": "Lebap",
    "country_id": "224"
  }, {
    "id": "3751",
    "name": "Mari",
    "country_id": "224"
  }, {
    "id": "3752",
    "name": "Grand Turk",
    "country_id": "225"
  }, {
    "id": "3753",
    "name": "South Caicos and East Caicos",
    "country_id": "225"
  }, {
    "id": "3754",
    "name": "Funafuti",
    "country_id": "226"
  }, {
    "id": "3755",
    "name": "Nanumanga",
    "country_id": "226"
  }, {
    "id": "3756",
    "name": "Nanumea",
    "country_id": "226"
  }, {
    "id": "3757",
    "name": "Niutao",
    "country_id": "226"
  }, {
    "id": "3758",
    "name": "Nui",
    "country_id": "226"
  }, {
    "id": "3759",
    "name": "Nukufetau",
    "country_id": "226"
  }, {
    "id": "3760",
    "name": "Nukulaelae",
    "country_id": "226"
  }, {
    "id": "3761",
    "name": "Vaitupu",
    "country_id": "226"
  }, {
    "id": "3762",
    "name": "Central",
    "country_id": "227"
  }, {
    "id": "3763",
    "name": "Eastern",
    "country_id": "227"
  }, {
    "id": "3764",
    "name": "Northern",
    "country_id": "227"
  }, {
    "id": "3765",
    "name": "Western",
    "country_id": "227"
  }, {
    "id": "3766",
    "name": "Cherkas'ka",
    "country_id": "228"
  }, {
    "id": "3767",
    "name": "Chernihivs'ka",
    "country_id": "228"
  }, {
    "id": "3768",
    "name": "Chernivets'ka",
    "country_id": "228"
  }, {
    "id": "3769",
    "name": "Crimea",
    "country_id": "228"
  }, {
    "id": "3770",
    "name": "Dnipropetrovska",
    "country_id": "228"
  }, {
    "id": "3771",
    "name": "Donets'ka",
    "country_id": "228"
  }, {
    "id": "3772",
    "name": "Ivano-Frankivs'ka",
    "country_id": "228"
  }, {
    "id": "3773",
    "name": "Kharkiv",
    "country_id": "228"
  }, {
    "id": "3774",
    "name": "Kharkov",
    "country_id": "228"
  }, {
    "id": "3775",
    "name": "Khersonska",
    "country_id": "228"
  }, {
    "id": "3776",
    "name": "Khmel'nyts'ka",
    "country_id": "228"
  }, {
    "id": "3777",
    "name": "Kirovohrad",
    "country_id": "228"
  }, {
    "id": "3778",
    "name": "Krym",
    "country_id": "228"
  }, {
    "id": "3779",
    "name": "Kyyiv",
    "country_id": "228"
  }, {
    "id": "3780",
    "name": "Kyyivs'ka",
    "country_id": "228"
  }, {
    "id": "3781",
    "name": "L'vivs'ka",
    "country_id": "228"
  }, {
    "id": "3782",
    "name": "Luhans'ka",
    "country_id": "228"
  }, {
    "id": "3783",
    "name": "Mykolayivs'ka",
    "country_id": "228"
  }, {
    "id": "3784",
    "name": "Odes'ka",
    "country_id": "228"
  }, {
    "id": "3785",
    "name": "Odessa",
    "country_id": "228"
  }, {
    "id": "3786",
    "name": "Poltavs'ka",
    "country_id": "228"
  }, {
    "id": "3787",
    "name": "Rivnens'ka",
    "country_id": "228"
  }, {
    "id": "3788",
    "name": "Sevastopol'",
    "country_id": "228"
  }, {
    "id": "3789",
    "name": "Sums'ka",
    "country_id": "228"
  }, {
    "id": "3790",
    "name": "Ternopil's'ka",
    "country_id": "228"
  }, {
    "id": "3791",
    "name": "Volyns'ka",
    "country_id": "228"
  }, {
    "id": "3792",
    "name": "Vynnyts'ka",
    "country_id": "228"
  }, {
    "id": "3793",
    "name": "Zakarpats'ka",
    "country_id": "228"
  }, {
    "id": "3794",
    "name": "Zaporizhia",
    "country_id": "228"
  }, {
    "id": "3795",
    "name": "Zhytomyrs'ka",
    "country_id": "228"
  }, {
    "id": "3796",
    "name": "Abu Zabi",
    "country_id": "229"
  }, {
    "id": "3797",
    "name": "Ajman",
    "country_id": "229"
  }, {
    "id": "3798",
    "name": "Dubai",
    "country_id": "229"
  }, {
    "id": "3799",
    "name": "Ras al-Khaymah",
    "country_id": "229"
  }, {
    "id": "3800",
    "name": "Sharjah",
    "country_id": "229"
  }, {
    "id": "3801",
    "name": "Sharjha",
    "country_id": "229"
  }, {
    "id": "3802",
    "name": "Umm al Qaywayn",
    "country_id": "229"
  }, {
    "id": "3803",
    "name": "al-Fujayrah",
    "country_id": "229"
  }, {
    "id": "3804",
    "name": "ash-Shariqah",
    "country_id": "229"
  }, {
    "id": "3805",
    "name": "Aberdeen",
    "country_id": "230"
  }, {
    "id": "3806",
    "name": "Aberdeenshire",
    "country_id": "230"
  }, {
    "id": "3807",
    "name": "Argyll",
    "country_id": "230"
  }, {
    "id": "3808",
    "name": "Armagh",
    "country_id": "230"
  }, {
    "id": "3809",
    "name": "Bedfordshire",
    "country_id": "230"
  }, {
    "id": "3810",
    "name": "Belfast",
    "country_id": "230"
  }, {
    "id": "3811",
    "name": "Berkshire",
    "country_id": "230"
  }, {
    "id": "3812",
    "name": "Birmingham",
    "country_id": "230"
  }, {
    "id": "3813",
    "name": "Brechin",
    "country_id": "230"
  }, {
    "id": "3814",
    "name": "Bridgnorth",
    "country_id": "230"
  }, {
    "id": "3815",
    "name": "Bristol",
    "country_id": "230"
  }, {
    "id": "3816",
    "name": "Buckinghamshire",
    "country_id": "230"
  }, {
    "id": "3817",
    "name": "Cambridge",
    "country_id": "230"
  }, {
    "id": "3818",
    "name": "Cambridgeshire",
    "country_id": "230"
  }, {
    "id": "3819",
    "name": "Channel Islands",
    "country_id": "230"
  }, {
    "id": "3820",
    "name": "Cheshire",
    "country_id": "230"
  }, {
    "id": "3821",
    "name": "Cleveland",
    "country_id": "230"
  }, {
    "id": "3822",
    "name": "Co Fermanagh",
    "country_id": "230"
  }, {
    "id": "3823",
    "name": "Conwy",
    "country_id": "230"
  }, {
    "id": "3824",
    "name": "Cornwall",
    "country_id": "230"
  }, {
    "id": "3825",
    "name": "Coventry",
    "country_id": "230"
  }, {
    "id": "3826",
    "name": "Craven Arms",
    "country_id": "230"
  }, {
    "id": "3827",
    "name": "Cumbria",
    "country_id": "230"
  }, {
    "id": "3828",
    "name": "Denbighshire",
    "country_id": "230"
  }, {
    "id": "3829",
    "name": "Derby",
    "country_id": "230"
  }, {
    "id": "3830",
    "name": "Derbyshire",
    "country_id": "230"
  }, {
    "id": "3831",
    "name": "Devon",
    "country_id": "230"
  }, {
    "id": "3832",
    "name": "Dial Code Dungannon",
    "country_id": "230"
  }, {
    "id": "3833",
    "name": "Didcot",
    "country_id": "230"
  }, {
    "id": "3834",
    "name": "Dorset",
    "country_id": "230"
  }, {
    "id": "3835",
    "name": "Dunbartonshire",
    "country_id": "230"
  }, {
    "id": "3836",
    "name": "Durham",
    "country_id": "230"
  }, {
    "id": "3837",
    "name": "East Dunbartonshire",
    "country_id": "230"
  }, {
    "id": "3838",
    "name": "East Lothian",
    "country_id": "230"
  }, {
    "id": "3839",
    "name": "East Midlands",
    "country_id": "230"
  }, {
    "id": "3840",
    "name": "East Sussex",
    "country_id": "230"
  }, {
    "id": "3841",
    "name": "East Yorkshire",
    "country_id": "230"
  }, {
    "id": "3842",
    "name": "England",
    "country_id": "230"
  }, {
    "id": "3843",
    "name": "Essex",
    "country_id": "230"
  }, {
    "id": "3844",
    "name": "Fermanagh",
    "country_id": "230"
  }, {
    "id": "3845",
    "name": "Fife",
    "country_id": "230"
  }, {
    "id": "3846",
    "name": "Flintshire",
    "country_id": "230"
  }, {
    "id": "3847",
    "name": "Fulham",
    "country_id": "230"
  }, {
    "id": "3848",
    "name": "Gainsborough",
    "country_id": "230"
  }, {
    "id": "3849",
    "name": "Glocestershire",
    "country_id": "230"
  }, {
    "id": "3850",
    "name": "Gwent",
    "country_id": "230"
  }, {
    "id": "3851",
    "name": "Hampshire",
    "country_id": "230"
  }, {
    "id": "3852",
    "name": "Hants",
    "country_id": "230"
  }, {
    "id": "3853",
    "name": "Herefordshire",
    "country_id": "230"
  }, {
    "id": "3854",
    "name": "Hertfordshire",
    "country_id": "230"
  }, {
    "id": "3855",
    "name": "Ireland",
    "country_id": "230"
  }, {
    "id": "3856",
    "name": "Isle Of Man",
    "country_id": "230"
  }, {
    "id": "3857",
    "name": "Isle of Wight",
    "country_id": "230"
  }, {
    "id": "3858",
    "name": "Kenford",
    "country_id": "230"
  }, {
    "id": "3859",
    "name": "Kent",
    "country_id": "230"
  }, {
    "id": "3860",
    "name": "Kilmarnock",
    "country_id": "230"
  }, {
    "id": "3861",
    "name": "Lanarkshire",
    "country_id": "230"
  }, {
    "id": "3862",
    "name": "Lancashire",
    "country_id": "230"
  }, {
    "id": "3863",
    "name": "Leicestershire",
    "country_id": "230"
  }, {
    "id": "3864",
    "name": "Lincolnshire",
    "country_id": "230"
  }, {
    "id": "3865",
    "name": "Llanymynech",
    "country_id": "230"
  }, {
    "id": "3866",
    "name": "London",
    "country_id": "230"
  }, {
    "id": "3867",
    "name": "Ludlow",
    "country_id": "230"
  }, {
    "id": "3868",
    "name": "Manchester",
    "country_id": "230"
  }, {
    "id": "3869",
    "name": "Mayfair",
    "country_id": "230"
  }, {
    "id": "3870",
    "name": "Merseyside",
    "country_id": "230"
  }, {
    "id": "3871",
    "name": "Mid Glamorgan",
    "country_id": "230"
  }, {
    "id": "3872",
    "name": "Middlesex",
    "country_id": "230"
  }, {
    "id": "3873",
    "name": "Mildenhall",
    "country_id": "230"
  }, {
    "id": "3874",
    "name": "Monmouthshire",
    "country_id": "230"
  }, {
    "id": "3875",
    "name": "Newton Stewart",
    "country_id": "230"
  }, {
    "id": "3876",
    "name": "Norfolk",
    "country_id": "230"
  }, {
    "id": "3877",
    "name": "North Humberside",
    "country_id": "230"
  }, {
    "id": "3878",
    "name": "North Yorkshire",
    "country_id": "230"
  }, {
    "id": "3879",
    "name": "Northamptonshire",
    "country_id": "230"
  }, {
    "id": "3880",
    "name": "Northants",
    "country_id": "230"
  }, {
    "id": "3881",
    "name": "Northern Ireland",
    "country_id": "230"
  }, {
    "id": "3882",
    "name": "Northumberland",
    "country_id": "230"
  }, {
    "id": "3883",
    "name": "Nottinghamshire",
    "country_id": "230"
  }, {
    "id": "3884",
    "name": "Oxford",
    "country_id": "230"
  }, {
    "id": "3885",
    "name": "Powys",
    "country_id": "230"
  }, {
    "id": "3886",
    "name": "Roos-shire",
    "country_id": "230"
  }, {
    "id": "3887",
    "name": "SUSSEX",
    "country_id": "230"
  }, {
    "id": "3888",
    "name": "Sark",
    "country_id": "230"
  }, {
    "id": "3889",
    "name": "Scotland",
    "country_id": "230"
  }, {
    "id": "3890",
    "name": "Scottish Borders",
    "country_id": "230"
  }, {
    "id": "3891",
    "name": "Shropshire",
    "country_id": "230"
  }, {
    "id": "3892",
    "name": "Somerset",
    "country_id": "230"
  }, {
    "id": "3893",
    "name": "South Glamorgan",
    "country_id": "230"
  }, {
    "id": "3894",
    "name": "South Wales",
    "country_id": "230"
  }, {
    "id": "3895",
    "name": "South Yorkshire",
    "country_id": "230"
  }, {
    "id": "3896",
    "name": "Southwell",
    "country_id": "230"
  }, {
    "id": "3897",
    "name": "Staffordshire",
    "country_id": "230"
  }, {
    "id": "3898",
    "name": "Strabane",
    "country_id": "230"
  }, {
    "id": "3899",
    "name": "Suffolk",
    "country_id": "230"
  }, {
    "id": "3900",
    "name": "Surrey",
    "country_id": "230"
  }, {
    "id": "3901",
    "name": "Sussex",
    "country_id": "230"
  }, {
    "id": "3902",
    "name": "Twickenham",
    "country_id": "230"
  }, {
    "id": "3903",
    "name": "Tyne and Wear",
    "country_id": "230"
  }, {
    "id": "3904",
    "name": "Tyrone",
    "country_id": "230"
  }, {
    "id": "3905",
    "name": "Utah",
    "country_id": "230"
  }, {
    "id": "3906",
    "name": "Wales",
    "country_id": "230"
  }, {
    "id": "3907",
    "name": "Warwickshire",
    "country_id": "230"
  }, {
    "id": "3908",
    "name": "West Lothian",
    "country_id": "230"
  }, {
    "id": "3909",
    "name": "West Midlands",
    "country_id": "230"
  }, {
    "id": "3910",
    "name": "West Sussex",
    "country_id": "230"
  }, {
    "id": "3911",
    "name": "West Yorkshire",
    "country_id": "230"
  }, {
    "id": "3912",
    "name": "Whissendine",
    "country_id": "230"
  }, {
    "id": "3913",
    "name": "Wiltshire",
    "country_id": "230"
  }, {
    "id": "3914",
    "name": "Wokingham",
    "country_id": "230"
  }, {
    "id": "3915",
    "name": "Worcestershire",
    "country_id": "230"
  }, {
    "id": "3916",
    "name": "Wrexham",
    "country_id": "230"
  }, {
    "id": "3917",
    "name": "Wurttemberg",
    "country_id": "230"
  }, {
    "id": "3918",
    "name": "Yorkshire",
    "country_id": "230"
  }, {
    "id": "3919",
    "name": "Alabama",
    "country_id": "231"
  }, {
    "id": "3920",
    "name": "Alaska",
    "country_id": "231"
  }, {
    "id": "3921",
    "name": "Arizona",
    "country_id": "231"
  }, {
    "id": "3922",
    "name": "Arkansas",
    "country_id": "231"
  }, {
    "id": "3923",
    "name": "Byram",
    "country_id": "231"
  }, {
    "id": "3924",
    "name": "California",
    "country_id": "231"
  }, {
    "id": "3925",
    "name": "Cokato",
    "country_id": "231"
  }, {
    "id": "3926",
    "name": "Colorado",
    "country_id": "231"
  }, {
    "id": "3927",
    "name": "Connecticut",
    "country_id": "231"
  }, {
    "id": "3928",
    "name": "Delaware",
    "country_id": "231"
  }, {
    "id": "3929",
    "name": "District of Columbia",
    "country_id": "231"
  }, {
    "id": "3930",
    "name": "Florida",
    "country_id": "231"
  }, {
    "id": "3931",
    "name": "Georgia",
    "country_id": "231"
  }, {
    "id": "3932",
    "name": "Hawaii",
    "country_id": "231"
  }, {
    "id": "3933",
    "name": "Idaho",
    "country_id": "231"
  }, {
    "id": "3934",
    "name": "Illinois",
    "country_id": "231"
  }, {
    "id": "3935",
    "name": "Indiana",
    "country_id": "231"
  }, {
    "id": "3936",
    "name": "Iowa",
    "country_id": "231"
  }, {
    "id": "3937",
    "name": "Kansas",
    "country_id": "231"
  }, {
    "id": "3938",
    "name": "Kentucky",
    "country_id": "231"
  }, {
    "id": "3939",
    "name": "Louisiana",
    "country_id": "231"
  }, {
    "id": "3940",
    "name": "Lowa",
    "country_id": "231"
  }, {
    "id": "3941",
    "name": "Maine",
    "country_id": "231"
  }, {
    "id": "3942",
    "name": "Maryland",
    "country_id": "231"
  }, {
    "id": "3943",
    "name": "Massachusetts",
    "country_id": "231"
  }, {
    "id": "3944",
    "name": "Medfield",
    "country_id": "231"
  }, {
    "id": "3945",
    "name": "Michigan",
    "country_id": "231"
  }, {
    "id": "3946",
    "name": "Minnesota",
    "country_id": "231"
  }, {
    "id": "3947",
    "name": "Mississippi",
    "country_id": "231"
  }, {
    "id": "3948",
    "name": "Missouri",
    "country_id": "231"
  }, {
    "id": "3949",
    "name": "Montana",
    "country_id": "231"
  }, {
    "id": "3950",
    "name": "Nebraska",
    "country_id": "231"
  }, {
    "id": "3951",
    "name": "Nevada",
    "country_id": "231"
  }, {
    "id": "3952",
    "name": "New Hampshire",
    "country_id": "231"
  }, {
    "id": "3953",
    "name": "New Jersey",
    "country_id": "231"
  }, {
    "id": "3954",
    "name": "New Jersy",
    "country_id": "231"
  }, {
    "id": "3955",
    "name": "New Mexico",
    "country_id": "231"
  }, {
    "id": "3956",
    "name": "New York",
    "country_id": "231"
  }, {
    "id": "3957",
    "name": "North Carolina",
    "country_id": "231"
  }, {
    "id": "3958",
    "name": "North Dakota",
    "country_id": "231"
  }, {
    "id": "3959",
    "name": "Ohio",
    "country_id": "231"
  }, {
    "id": "3960",
    "name": "Oklahoma",
    "country_id": "231"
  }, {
    "id": "3961",
    "name": "Ontario",
    "country_id": "231"
  }, {
    "id": "3962",
    "name": "Oregon",
    "country_id": "231"
  }, {
    "id": "3963",
    "name": "Pennsylvania",
    "country_id": "231"
  }, {
    "id": "3964",
    "name": "Ramey",
    "country_id": "231"
  }, {
    "id": "3965",
    "name": "Rhode Island",
    "country_id": "231"
  }, {
    "id": "3966",
    "name": "South Carolina",
    "country_id": "231"
  }, {
    "id": "3967",
    "name": "South Dakota",
    "country_id": "231"
  }, {
    "id": "3968",
    "name": "Sublimity",
    "country_id": "231"
  }, {
    "id": "3969",
    "name": "Tennessee",
    "country_id": "231"
  }, {
    "id": "3970",
    "name": "Texas",
    "country_id": "231"
  }, {
    "id": "3971",
    "name": "Trimble",
    "country_id": "231"
  }, {
    "id": "3972",
    "name": "Utah",
    "country_id": "231"
  }, {
    "id": "3973",
    "name": "Vermont",
    "country_id": "231"
  }, {
    "id": "3974",
    "name": "Virginia",
    "country_id": "231"
  }, {
    "id": "3975",
    "name": "Washington",
    "country_id": "231"
  }, {
    "id": "3976",
    "name": "West Virginia",
    "country_id": "231"
  }, {
    "id": "3977",
    "name": "Wisconsin",
    "country_id": "231"
  }, {
    "id": "3978",
    "name": "Wyoming",
    "country_id": "231"
  }, {
    "id": "3979",
    "name": "United States Minor Outlying I",
    "country_id": "232"
  }, {
    "id": "3980",
    "name": "Artigas",
    "country_id": "233"
  }, {
    "id": "3981",
    "name": "Canelones",
    "country_id": "233"
  }, {
    "id": "3982",
    "name": "Cerro Largo",
    "country_id": "233"
  }, {
    "id": "3983",
    "name": "Colonia",
    "country_id": "233"
  }, {
    "id": "3984",
    "name": "Durazno",
    "country_id": "233"
  }, {
    "id": "3985",
    "name": "FLorida",
    "country_id": "233"
  }, {
    "id": "3986",
    "name": "Flores",
    "country_id": "233"
  }, {
    "id": "3987",
    "name": "Lavalleja",
    "country_id": "233"
  }, {
    "id": "3988",
    "name": "Maldonado",
    "country_id": "233"
  }, {
    "id": "3989",
    "name": "Montevideo",
    "country_id": "233"
  }, {
    "id": "3990",
    "name": "Paysandu",
    "country_id": "233"
  }, {
    "id": "3991",
    "name": "Rio Negro",
    "country_id": "233"
  }, {
    "id": "3992",
    "name": "Rivera",
    "country_id": "233"
  }, {
    "id": "3993",
    "name": "Rocha",
    "country_id": "233"
  }, {
    "id": "3994",
    "name": "Salto",
    "country_id": "233"
  }, {
    "id": "3995",
    "name": "San Jose",
    "country_id": "233"
  }, {
    "id": "3996",
    "name": "Soriano",
    "country_id": "233"
  }, {
    "id": "3997",
    "name": "Tacuarembo",
    "country_id": "233"
  }, {
    "id": "3998",
    "name": "Treinta y Tres",
    "country_id": "233"
  }, {
    "id": "3999",
    "name": "Andijon",
    "country_id": "234"
  }, {
    "id": "4000",
    "name": "Buhoro",
    "country_id": "234"
  }, {
    "id": "4001",
    "name": "Buxoro Viloyati",
    "country_id": "234"
  }, {
    "id": "4002",
    "name": "Cizah",
    "country_id": "234"
  }, {
    "id": "4003",
    "name": "Fargona",
    "country_id": "234"
  }, {
    "id": "4004",
    "name": "Horazm",
    "country_id": "234"
  }, {
    "id": "4005",
    "name": "Kaskadar",
    "country_id": "234"
  }, {
    "id": "4006",
    "name": "Korakalpogiston",
    "country_id": "234"
  }, {
    "id": "4007",
    "name": "Namangan",
    "country_id": "234"
  }, {
    "id": "4008",
    "name": "Navoi",
    "country_id": "234"
  }, {
    "id": "4009",
    "name": "Samarkand",
    "country_id": "234"
  }, {
    "id": "4010",
    "name": "Sirdare",
    "country_id": "234"
  }, {
    "id": "4011",
    "name": "Surhondar",
    "country_id": "234"
  }, {
    "id": "4012",
    "name": "Toskent",
    "country_id": "234"
  }, {
    "id": "4013",
    "name": "Malampa",
    "country_id": "235"
  }, {
    "id": "4014",
    "name": "Penama",
    "country_id": "235"
  }, {
    "id": "4015",
    "name": "Sanma",
    "country_id": "235"
  }, {
    "id": "4016",
    "name": "Shefa",
    "country_id": "235"
  }, {
    "id": "4017",
    "name": "Tafea",
    "country_id": "235"
  }, {
    "id": "4018",
    "name": "Torba",
    "country_id": "235"
  }, {
    "id": "4019",
    "name": "Vatican City State (Holy See)",
    "country_id": "236"
  }, {
    "id": "4020",
    "name": "Amazonas",
    "country_id": "237"
  }, {
    "id": "4021",
    "name": "Anzoategui",
    "country_id": "237"
  }, {
    "id": "4022",
    "name": "Apure",
    "country_id": "237"
  }, {
    "id": "4023",
    "name": "Aragua",
    "country_id": "237"
  }, {
    "id": "4024",
    "name": "Barinas",
    "country_id": "237"
  }, {
    "id": "4025",
    "name": "Bolivar",
    "country_id": "237"
  }, {
    "id": "4026",
    "name": "Carabobo",
    "country_id": "237"
  }, {
    "id": "4027",
    "name": "Cojedes",
    "country_id": "237"
  }, {
    "id": "4028",
    "name": "Delta Amacuro",
    "country_id": "237"
  }, {
    "id": "4029",
    "name": "Distrito Federal",
    "country_id": "237"
  }, {
    "id": "4030",
    "name": "Falcon",
    "country_id": "237"
  }, {
    "id": "4031",
    "name": "Guarico",
    "country_id": "237"
  }, {
    "id": "4032",
    "name": "Lara",
    "country_id": "237"
  }, {
    "id": "4033",
    "name": "Merida",
    "country_id": "237"
  }, {
    "id": "4034",
    "name": "Miranda",
    "country_id": "237"
  }, {
    "id": "4035",
    "name": "Monagas",
    "country_id": "237"
  }, {
    "id": "4036",
    "name": "Nueva Esparta",
    "country_id": "237"
  }, {
    "id": "4037",
    "name": "Portuguesa",
    "country_id": "237"
  }, {
    "id": "4038",
    "name": "Sucre",
    "country_id": "237"
  }, {
    "id": "4039",
    "name": "Tachira",
    "country_id": "237"
  }, {
    "id": "4040",
    "name": "Trujillo",
    "country_id": "237"
  }, {
    "id": "4041",
    "name": "Vargas",
    "country_id": "237"
  }, {
    "id": "4042",
    "name": "Yaracuy",
    "country_id": "237"
  }, {
    "id": "4043",
    "name": "Zulia",
    "country_id": "237"
  }, {
    "id": "4044",
    "name": "Bac Giang",
    "country_id": "238"
  }, {
    "id": "4045",
    "name": "Binh Dinh",
    "country_id": "238"
  }, {
    "id": "4046",
    "name": "Binh Duong",
    "country_id": "238"
  }, {
    "id": "4047",
    "name": "Da Nang",
    "country_id": "238"
  }, {
    "id": "4048",
    "name": "Dong Bang Song Cuu Long",
    "country_id": "238"
  }, {
    "id": "4049",
    "name": "Dong Bang Song Hong",
    "country_id": "238"
  }, {
    "id": "4050",
    "name": "Dong Nai",
    "country_id": "238"
  }, {
    "id": "4051",
    "name": "Dong Nam Bo",
    "country_id": "238"
  }, {
    "id": "4052",
    "name": "Duyen Hai Mien Trung",
    "country_id": "238"
  }, {
    "id": "4053",
    "name": "Hanoi",
    "country_id": "238"
  }, {
    "id": "4054",
    "name": "Hung Yen",
    "country_id": "238"
  }, {
    "id": "4055",
    "name": "Khu Bon Cu",
    "country_id": "238"
  }, {
    "id": "4056",
    "name": "Long An",
    "country_id": "238"
  }, {
    "id": "4057",
    "name": "Mien Nui Va Trung Du",
    "country_id": "238"
  }, {
    "id": "4058",
    "name": "Thai Nguyen",
    "country_id": "238"
  }, {
    "id": "4059",
    "name": "Thanh Pho Ho Chi Minh",
    "country_id": "238"
  }, {
    "id": "4060",
    "name": "Thu Do Ha Noi",
    "country_id": "238"
  }, {
    "id": "4061",
    "name": "Tinh Can Tho",
    "country_id": "238"
  }, {
    "id": "4062",
    "name": "Tinh Da Nang",
    "country_id": "238"
  }, {
    "id": "4063",
    "name": "Tinh Gia Lai",
    "country_id": "238"
  }, {
    "id": "4064",
    "name": "Anegada",
    "country_id": "239"
  }, {
    "id": "4065",
    "name": "Jost van Dyke",
    "country_id": "239"
  }, {
    "id": "4066",
    "name": "Tortola",
    "country_id": "239"
  }, {
    "id": "4067",
    "name": "Saint Croix",
    "country_id": "240"
  }, {
    "id": "4068",
    "name": "Saint John",
    "country_id": "240"
  }, {
    "id": "4069",
    "name": "Saint Thomas",
    "country_id": "240"
  }, {
    "id": "4070",
    "name": "Alo",
    "country_id": "241"
  }, {
    "id": "4071",
    "name": "Singave",
    "country_id": "241"
  }, {
    "id": "4072",
    "name": "Wallis",
    "country_id": "241"
  }, {
    "id": "4073",
    "name": "Bu Jaydur",
    "country_id": "242"
  }, {
    "id": "4074",
    "name": "Wad-adh-Dhahab",
    "country_id": "242"
  }, {
    "id": "4075",
    "name": "al-'Ayun",
    "country_id": "242"
  }, {
    "id": "4076",
    "name": "as-Samarah",
    "country_id": "242"
  }, {
    "id": "4077",
    "name": "'Adan",
    "country_id": "243"
  }, {
    "id": "4078",
    "name": "Abyan",
    "country_id": "243"
  }, {
    "id": "4079",
    "name": "Dhamar",
    "country_id": "243"
  }, {
    "id": "4080",
    "name": "Hadramaut",
    "country_id": "243"
  }, {
    "id": "4081",
    "name": "Hajjah",
    "country_id": "243"
  }, {
    "id": "4082",
    "name": "Hudaydah",
    "country_id": "243"
  }, {
    "id": "4083",
    "name": "Ibb",
    "country_id": "243"
  }, {
    "id": "4084",
    "name": "Lahij",
    "country_id": "243"
  }, {
    "id": "4085",
    "name": "Ma'rib",
    "country_id": "243"
  }, {
    "id": "4086",
    "name": "Madinat San'a",
    "country_id": "243"
  }, {
    "id": "4087",
    "name": "Sa'dah",
    "country_id": "243"
  }, {
    "id": "4088",
    "name": "Sana",
    "country_id": "243"
  }, {
    "id": "4089",
    "name": "Shabwah",
    "country_id": "243"
  }, {
    "id": "4090",
    "name": "Ta'izz",
    "country_id": "243"
  }, {
    "id": "4091",
    "name": "al-Bayda",
    "country_id": "243"
  }, {
    "id": "4092",
    "name": "al-Hudaydah",
    "country_id": "243"
  }, {
    "id": "4093",
    "name": "al-Jawf",
    "country_id": "243"
  }, {
    "id": "4094",
    "name": "al-Mahrah",
    "country_id": "243"
  }, {
    "id": "4095",
    "name": "al-Mahwit",
    "country_id": "243"
  }, {
    "id": "4096",
    "name": "Central Serbia",
    "country_id": "244"
  }, {
    "id": "4097",
    "name": "Kosovo and Metohija",
    "country_id": "244"
  }, {
    "id": "4098",
    "name": "Montenegro",
    "country_id": "244"
  }, {
    "id": "4099",
    "name": "Republic of Serbia",
    "country_id": "244"
  }, {
    "id": "4100",
    "name": "Serbia",
    "country_id": "244"
  }, {
    "id": "4101",
    "name": "Vojvodina",
    "country_id": "244"
  }, {
    "id": "4102",
    "name": "Central",
    "country_id": "245"
  }, {
    "id": "4103",
    "name": "Copperbelt",
    "country_id": "245"
  }, {
    "id": "4104",
    "name": "Eastern",
    "country_id": "245"
  }, {
    "id": "4105",
    "name": "Luapala",
    "country_id": "245"
  }, {
    "id": "4106",
    "name": "Lusaka",
    "country_id": "245"
  }, {
    "id": "4107",
    "name": "North-Western",
    "country_id": "245"
  }, {
    "id": "4108",
    "name": "Northern",
    "country_id": "245"
  }, {
    "id": "4109",
    "name": "Southern",
    "country_id": "245"
  }, {
    "id": "4110",
    "name": "Western",
    "country_id": "245"
  }, {
    "id": "4111",
    "name": "Bulawayo",
    "country_id": "246"
  }, {
    "id": "4112",
    "name": "Harare",
    "country_id": "246"
  }, {
    "id": "4113",
    "name": "Manicaland",
    "country_id": "246"
  }, {
    "id": "4114",
    "name": "Mashonaland Central",
    "country_id": "246"
  }, {
    "id": "4115",
    "name": "Mashonaland East",
    "country_id": "246"
  }, {
    "id": "4116",
    "name": "Mashonaland West",
    "country_id": "246"
  }, {
    "id": "4117",
    "name": "Masvingo",
    "country_id": "246"
  }, {
    "id": "4118",
    "name": "Matabeleland North",
    "country_id": "246"
  }, {
    "id": "4119",
    "name": "Matabeleland South",
    "country_id": "246"
  }, {
    "id": "4120",
    "name": "Midlands",
    "country_id": "246"
  }, {
    "id": "4121",
    "name": "Lienchiang County",
    "country_id": "214"
  }];
  var states$1 = states.map(function (stat) {
    return _objectSpread2({
      label: stat.name
    }, stat);
  });

  var getAllCountries = function getAllCountries() {
    return countries$1;
  }; // This is just for testing purpose only, to be sure that the states are complete
  var getStatesByCountryId = function getStatesByCountryId(countryId) {
    var statesForCountry = states$1.filter(function (state) {
      return String(state.country_id) === String(countryId);
    });
    return statesForCountry;
  };

  var selectedCountry = null;
  function CountryReactSelect(props) {
    // const [countryStates, setCountryState] = useState([]);
    var handleChange = function handleChange(selectedOption) {
      selectedCountry = selectedOption.id;
    };

    return /*#__PURE__*/React__default.createElement("div", null, /*#__PURE__*/React__default.createElement(index // value={selectedOption}
    , _extends({
      onChange: handleChange
    }, props, {
      options: getAllCountries()
    })));
  }
  function StateReactSelect() {
    var handleChange = function handleChange() {
      console.log('doing nothing');
    };

    return /*#__PURE__*/React__default.createElement("div", null, /*#__PURE__*/React__default.createElement(index // value={selectedOption}
    , {
      onChange: handleChange,
      options: getStatesByCountryId(selectedCountry)
    }));
  }

  // export { default as Button } from "components/Button";
  var index$1 = {
    CountryReactSelect: CountryReactSelect,
    StateReactSelect: StateReactSelect
  };

  return index$1;

})));
