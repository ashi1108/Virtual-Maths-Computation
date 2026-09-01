const innerUploadImage = document.querySelector(".inner-upload-image")
const input = innerUploadImage.querySelector("input")
const questionInput = document.querySelector("#question")
const solveButton = document.querySelector("#solveButton")
const playStepsButton = document.querySelector("#playStepsButton")
const output = document.querySelector(".output")
const summary = document.querySelector("#summary")
const stepOutput = document.querySelector("#stepOutput")
const languageSelect = document.querySelector("#languageSelect")

const allowedNames = new Set([
    "sin", "cos", "tan", "asin", "acos", "atan", "log", "ln", "exp", "sqrt", "abs",
    "floor", "ceil", "round", "max", "min", "gcd", "lcm", "mod", "pi", "e", "i",
    "complex", "re", "im", "conj", "arg", "matrix", "det", "transpose", "inv", "trace", "rank",
    "add", "sub", "mul", "div", "limit", "derivative", "solve", "x"
])

function isComplex(value) {
    return value && typeof value === "object" && typeof value.re === "number" && typeof value.im === "number"
}

function complex(a, b = 0) {
    return { re: Number(a), im: Number(b) }
}

function complexToString(value) {
    if (!isComplex(value)) return String(value)
    const rePart = Number(value.re.toFixed(10))
    const imPart = Number(value.im.toFixed(10))
    const reString = rePart === 0 ? "" : `${rePart}`
    const imString = imPart === 0 ? "" : `${imPart === 1 ? "" : imPart === -1 ? "-" : imPart}i`
    if (reString && imString) {
        return `${reString}${imPart >= 0 ? "+" : ""}${imString}`
    }
    return reString || imString || "0"
}

function complexify(value) {
    if (isComplex(value)) return value
    return complex(Number(value), 0)
}

function complexAdd(a, b) {
    const x = complexify(a)
    const y = complexify(b)
    return complex(x.re + y.re, x.im + y.im)
}

function complexSub(a, b) {
    const x = complexify(a)
    const y = complexify(b)
    return complex(x.re - y.re, x.im - y.im)
}

function complexMul(a, b) {
    const x = complexify(a)
    const y = complexify(b)
    return complex(x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re)
}

function complexDiv(a, b) {
    const x = complexify(a)
    const y = complexify(b)
    const denom = y.re * y.re + y.im * y.im
    if (denom === 0) throw new Error("Division by zero in complex arithmetic.")
    return complex((x.re * y.re + x.im * y.im) / denom, (x.im * y.re - x.re * y.im) / denom)
}

function complexExp(z) {
    const x = complexify(z)
    const expx = Math.exp(x.re)
    return complex(expx * Math.cos(x.im), expx * Math.sin(x.im))
}

function complexLog(z) {
    const x = complexify(z)
    const modulus = Math.hypot(x.re, x.im)
    const angle = Math.atan2(x.im, x.re)
    return complex(Math.log(modulus), angle)
}

function complexSin(z) {
    const x = complexify(z)
    return complex(
        Math.sin(x.re) * Math.cosh(x.im),
        Math.cos(x.re) * Math.sinh(x.im)
    )
}

function complexCos(z) {
    const x = complexify(z)
    return complex(
        Math.cos(x.re) * Math.cosh(x.im),
        -Math.sin(x.re) * Math.sinh(x.im)
    )
}

function complexTan(z) {
    const s = complexSin(z)
    const c = complexCos(z)
    return complexDiv(s, c)
}

function matrixShape(matrix) {
    if (!Array.isArray(matrix) || matrix.length === 0) return null
    const rows = matrix.length
    const cols = matrix[0].length
    for (const row of matrix) {
        if (!Array.isArray(row) || row.length !== cols) throw new Error("Matrix rows must all have the same length.")
    }
    return { rows, cols }
}

function matrixTranspose(matrix) {
    const shape = matrixShape(matrix)
    if (!shape) throw new Error("Invalid matrix.")
    const result = Array.from({ length: shape.cols }, () => Array(shape.rows).fill(0))
    for (let i = 0; i < shape.rows; i++) {
        for (let j = 0; j < shape.cols; j++) {
            result[j][i] = matrix[i][j]
        }
    }
    return result
}

function matrixMultiply(A, B) {
    const shapeA = matrixShape(A)
    const shapeB = matrixShape(B)
    if (!shapeA || !shapeB) throw new Error("Both values must be matrices.")
    if (shapeA.cols !== shapeB.rows) throw new Error("Matrix multiplication requires inner dimensions to match.")
    const result = Array.from({ length: shapeA.rows }, () => Array(shapeB.cols).fill(0))
    for (let i = 0; i < shapeA.rows; i++) {
        for (let j = 0; j < shapeB.cols; j++) {
            let sum = 0
            for (let k = 0; k < shapeA.cols; k++) {
                sum += A[i][k] * B[k][j]
            }
            result[i][j] = sum
        }
    }
    return result
}

function matrixDet(matrix) {
    const shape = matrixShape(matrix)
    if (!shape || shape.rows !== shape.cols) throw new Error("Determinant requires a square matrix.")
    const n = shape.rows
    if (n === 1) return matrix[0][0]
    if (n === 2) return matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0]
    let det = 0
    for (let col = 0; col < n; col++) {
        const submatrix = matrix.slice(1).map(row => row.filter((_, index) => index !== col))
        det += ((col % 2 === 0 ? 1 : -1) * matrix[0][col] * matrixDet(submatrix))
    }
    return det
}

function matrixTrace(matrix) {
    const shape = matrixShape(matrix)
    if (!shape || shape.rows !== shape.cols) throw new Error("Trace requires a square matrix.")
    let sum = 0
    for (let i = 0; i < shape.rows; i++) sum += matrix[i][i]
    return sum
}

function matrixInverse(matrix) {
    const shape = matrixShape(matrix)
    if (!shape || shape.rows !== shape.cols) throw new Error("Inverse requires a square matrix.")
    const n = shape.rows
    const A = matrix.map(row => row.slice())
    const inverse = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => (i === j ? 1 : 0)))
    for (let i = 0; i < n; i++) {
        let pivot = i
        for (let row = i; row < n; row++) {
            if (Math.abs(A[row][i]) > Math.abs(A[pivot][i])) pivot = row
        }
        if (A[pivot][i] === 0) throw new Error("Matrix is singular and not invertible.")
        ;[A[i], A[pivot]] = [A[pivot], A[i]]
        ;[inverse[i], inverse[pivot]] = [inverse[pivot], inverse[i]]
        const divisor = A[i][i]
        for (let col = 0; col < n; col++) {
            A[i][col] /= divisor
            inverse[i][col] /= divisor
        }
        for (let row = 0; row < n; row++) {
            if (row !== i) {
                const factor = A[row][i]
                for (let col = 0; col < n; col++) {
                    A[row][col] -= factor * A[i][col]
                    inverse[row][col] -= factor * inverse[i][col]
                }
            }
        }
    }
    return inverse
}

function matrixRank(matrix) {
    const shape = matrixShape(matrix)
    if (!shape) throw new Error("Rank requires a valid matrix.")
    const A = matrix.map(row => row.slice())
    const rows = shape.rows
    const cols = shape.cols
    let rank = 0
    for (let col = 0; col < cols; col++) {
        let pivot = rank
        while (pivot < rows && A[pivot][col] === 0) pivot++
        if (pivot === rows) continue
        ;[A[rank], A[pivot]] = [A[pivot], A[rank]]
        const divisor = A[rank][col]
        for (let j = col; j < cols; j++) A[rank][j] /= divisor
        for (let row = 0; row < rows; row++) {
            if (row !== rank) {
                const factor = A[row][col]
                for (let j = col; j < cols; j++) A[row][j] -= factor * A[rank][j]
            }
        }
        rank++
    }
    return rank
}

function toFraction(value) {
    const tolerance = 1e-10
    let x = Number(value)
    if (Number.isInteger(x)) return `${x}`
    let sign = x < 0 ? -1 : 1
    x = Math.abs(x)
    let numerator = 1
    let denominator = 0
    let previousNumerator = 0
    let previousDenominator = 1
    let valueCopy = x
    while (true) {
        const a = Math.floor(valueCopy)
        const tempNumerator = numerator
        numerator = a * numerator + previousNumerator
        previousNumerator = tempNumerator
        const tempDenominator = denominator
        denominator = a * denominator + previousDenominator
        previousDenominator = tempDenominator
        const approximation = numerator / denominator
        if (Math.abs(approximation - x) < tolerance || denominator > 1000) break
        valueCopy = 1 / (valueCopy - a)
        if (!isFinite(valueCopy)) break
    }
    return `${sign * numerator}/${denominator}`
}

function formatResult(result) {
    if (isComplex(result)) return complexToString(result)
    if (Array.isArray(result)) {
        return result.map(row => Array.isArray(row) ? `[ ${row.map(formatResult).join(", ")} ]` : formatResult(row)).join("\n")
    }
    if (typeof result === "number") {
        if (Number.isInteger(result)) return `${result}`
        const fraction = toFraction(result)
        return `${result} (${fraction})`
    }
    return String(result)
}

const translations = {
    english: {
        step: "Step",
        problem: "Problem",
        answer: "Answer",
        evaluating: "Evaluating expression",
        equationType: "This is an equation.",
        expressionType: "This is an expression.",
        parseExpression: "First, clean the problem and prepare it for evaluation.",
        orderOfOperations: "Then use the order of operations: parentheses, exponents, multiply/divide, add/subtract.",
        result: "Result",
        solvingEquation: "Solving the equation using interval search.",
        evaluateAt: "Evaluate at",
        foundRoot: "Found a root after narrowing the interval.",
        usingFunction: "Using the math function",
        trySimpler: "If this is too hard, try a simpler expression or use solve(...) with a variable.",
        limitStep: "Estimate the limit by approaching the point from both sides.",
        derivativeStep: "Approximate the derivative using a small difference near the point.",
        solveFunctionStep: "Solve the equation to find the value of the variable.",
        translationHint: "Translated step-by-step support for new learners."
    },
    hindi: {
        step: "कदम",
        problem: "समस्या",
        answer: "उत्तर",
        evaluating: "व्यंजक का मान निकालना",
        equationType: "यह एक समीकरण है।",
        expressionType: "यह एक व्यंजक है।",
        parseExpression: "पहले समस्या को साफ़ करें और मूल्यांकन के लिए तैयार करें।",
        orderOfOperations: "फिर संचालन के क्रम का उपयोग करें: कोष्ठक, घात, गुणा/भाग, जोड़/घटाव।",
        result: "परिणाम",
        solvingEquation: "इंटरवल खोज का उपयोग करके समीकरण हल कर रहे हैं।",
        evaluateAt: "यहाँ पर मान निकालें",
        foundRoot: "अंतर कम करने के बाद जड़ मिली।",
        usingFunction: "गणित फ़ंक्शन का उपयोग करना",
        trySimpler: "यदि यह बहुत कठिन हो, तो एक सरल व्यंजक आज़माएँ या solve(...) का उपयोग करें।",
        limitStep: "बिंदु के दोनों ओर से पास करके सीमा का अनुमान लगाएँ।",
        derivativeStep: "बिंदु के पास एक छोटे अंतर का उपयोग करके अवकलन का अनुमान लगाएँ।",
        solveFunctionStep: "चर का मान खोजने के लिए समीकरण हल करें।",
        translationHint: "नए शिक्षार्थियों के लिए अनुवादित चरण-दर-चरण सहायता।"
    },
    malayalam: {
        step: "പടി",
        problem: "പ്രശ്നം",
        answer: "ഉത്തരം",
        evaluating: "പ്രഖ്യാപനം വിലയിരുത്തൽ",
        equationType: "ഇത് ഒരു സമവാക്യം ആണ്.",
        expressionType: "ഇത് ഒരു പ്രകടനമാണ്.",
        parseExpression: "ആദ്യമായി പ്രശ്നം ശുദ്ധീകരിച്ച് വിലയിരുത്തലിന് തയ്യാറാക്കുക.",
        orderOfOperations: "ശേഷം പ്രവർത്തനക്രമം ഉപയോഗിക്കുക: അവയവങ്ങൾ, ഘാതം, ഗുണനം/ഭാഗം, കൂട്ടം/വിയോഗം.",
        result: "ഫലം",
        solvingEquation: "ഇന്റർവൽ തിരച്ചിൽ ഉപയോഗിച്ച് സമവാക്യം പരിഹരിക്കുന്നു.",
        evaluateAt: "ഇവിടെ മൂല്യം കണ്ടെത്തുക",
        foundRoot: "ഇന്റർവൽ കുറച്ചപ്പോൾ മൂല്യം കണ്ടെത്തി.",
        usingFunction: "ഗണിത ഫംഗ്ഷൻ ഉപയോഗിക്കുന്നു",
        trySimpler: "ഇത് വളരെ കഠിനമാണെങ്കിൽ, ഒരു ലളിതമായ പ്രകടനം പരീക്ഷിക്കുകയോ solve(...) ഉപയോഗിക്കുകയോ ചെയ്യൂ.",
        limitStep: "ബിന്ദുവിന്റെ ഇരുവശത്തേക്കും സമീപിച്ച് പരിധി ഏകദേശം കണക്കാക്കുക.",
        derivativeStep: "ബിന്ദുവിന് സമീപമുള്ള ചെറിയ വ്യത്യാസം ഉപയോഗിച്ച് വ്യുത്പന്നം ഏകദേശം കണക്കാക്കുക.",
        solveFunctionStep: "ചരത്തിന്റെ മൂല്യം കണ്ടെത്താൻ സമവാക്യം പരിഹരിക്കുന്നു.",
        translationHint: "പുതിയ പഠിതാക്കൾക്കായുള്ള വിവർത്തനം ചെയ്ത ഘടക-ഘടക സഹായം."
    }
}

function t(key) {
    const current = languageSelect?.value || "english"
    return translations[current]?.[key] || translations.english[key] || key
}

function createStepLine(text, index, delay = 0) {
    const line = document.createElement("div")
    line.className = "step-line"
    line.textContent = `${index}. ${text}`
    line.style.animationDelay = `${delay}s`
    return line
}

function displaySteps(steps) {
    stepOutput.innerHTML = ""
    steps.forEach((step, index) => {
        stepOutput.appendChild(createStepLine(step, index + 1, index * 0.16))
    })
    updatePlayStepsButtonState()
}

function updatePlayStepsButtonState() {
    if (!playStepsButton) return
    const disabled = stepOutput.children.length === 0
    playStepsButton.disabled = disabled
    // show appropriate label
    playStepsButton.textContent = disabled ? "Play Steps" : (stepInterval ? "Pause" : "Play Steps")
}

function highlightStep(index) {
    const stepItems = [...stepOutput.querySelectorAll(".step-line")]
    stepItems.forEach((item, i) => {
        item.classList.toggle("active", i === index)
        if (i === index) {
            item.scrollIntoView({ behavior: "smooth", block: "nearest" })
        }
    })
}

function stopStepAnimation() {
    if (stepInterval) {
        clearInterval(stepInterval)
        stepInterval = null
    }
}

function startStepAnimation() {
    if (stepOutput.children.length === 0) return
    stopStepAnimation()
    currentStepIndex = 0
    highlightStep(currentStepIndex)
    stepInterval = setInterval(() => {
        currentStepIndex = (currentStepIndex + 1) % stepOutput.children.length
        highlightStep(currentStepIndex)
    }, 2500)
}

function togglePlaySteps() {
    if (!playStepsButton) return
    if (stepInterval) {
        stopStepAnimation()
        playStepsButton.textContent = "Play Steps"
    } else {
        startStepAnimation()
        playStepsButton.textContent = "Pause"
    }
}

function splitArguments(text) {
    const args = []
    let current = ""
    let depth = 0
    let inQuote = false
    let quoteChar = ""
    for (let i = 0; i < text.length; i++) {
        const chr = text[i]
        if ((chr === '"' || chr === "'") && text[i - 1] !== "\\") {
            if (inQuote && chr === quoteChar) {
                inQuote = false
                quoteChar = ""
            } else if (!inQuote) {
                inQuote = true
                quoteChar = chr
            }
            current += chr
            continue
        }
        if (!inQuote) {
            if (chr === "(") depth++
            if (chr === ")") depth = Math.max(0, depth - 1)
            if (chr === "," && depth === 0) {
                args.push(current.trim())
                current = ""
                continue
            }
        }
        current += chr
    }
    if (current.trim()) args.push(current.trim())
    return args
}

function createProblemSteps(problem) {
    const lang = languageSelect?.value || "english"
    const steps = []
    try {
        if (problem.startsWith("solve(")) {
            const inner = problem.slice(6, -1)
            const [equation, variableName] = splitArguments(inner)
            steps.push(t("solveFunctionStep"))
            steps.push(`${t("parseExpression")} ${equation} = 0 with variable ${variableName}.`)
            steps.push(t("orderOfOperations"))
            const result = solveEquation(equation)
            steps.push(`${t("foundRoot")} ${variableName} ≈ ${formatResult(result)}.`)
            return { result, steps }
        }
        if (problem.startsWith("limit(")) {
            const [expr, variable, point] = splitArguments(problem.slice(6, -1))
            steps.push(t("limitStep"))
            steps.push(`${t("parseExpression")} ${expr} where ${variable} → ${point}.`)
            steps.push(t("orderOfOperations"))
            const value = math.limit(expr.replace(/^['"]|['"]$/g, ""), variable, Number(point))
            steps.push(`${t("result")} ≈ ${formatResult(value)}.`)
            return { result: value, steps }
        }
        if (problem.startsWith("derivative(")) {
            const [expr, variable, point] = splitArguments(problem.slice(11, -1))
            steps.push(t("derivativeStep"))
            steps.push(`${t("parseExpression")} ${expr} at ${variable} = ${point}.`)
            steps.push(t("orderOfOperations"))
            const value = math.derivative(expr.replace(/^['"]|['"]$/g, ""), variable, Number(point))
            steps.push(`${t("result")} ≈ ${formatResult(value)}.`)
            return { result: value, steps }
        }
        if (problem.includes("=") && !problem.trim().startsWith("solve(")) {
            const [left, right] = problem.split("=")
            steps.push(t("equationType"))
            steps.push(`${t("parseExpression")} ${left.trim()} = ${right.trim()}.`)
            steps.push(t("orderOfOperations"))
            const solution = solveEquation(problem)
            const f = x => evaluateExpression(`${left} - (${right})`, x)
            const a = -1000
            const b = 1000
            steps.push(`${t("evaluateAt")} a=${a} → f(a) = ${formatResult(f(a))}`)
            steps.push(`${t("evaluateAt")} b=${b} → f(b) = ${formatResult(f(b))}`)
            steps.push(`${t("foundRoot")} x ≈ ${formatResult(solution.value)}.`)
            return { result: solution.value, steps: [...steps, ...solution.steps] }
        }
        steps.push(t("expressionType"))
        steps.push(`${t("parseExpression")} ${problem}.`)
        steps.push(t("orderOfOperations"))
        const value = evaluateExpression(problem)
        if (Number.isNaN(Number(value))) {
            steps.push(t("trySimpler"))
        }
        steps.push(`${t("result")} = ${formatResult(value)}.`)
        return { result: value, steps }
    } catch (error) {
        steps.push(error.message)
        return { result: null, steps }
    }
}

function generateResponse() {
    const problem = questionInput.value.trim()
    if (!problem) {
        output.style.display = "block"
        summary.textContent = t("problem") + ": " + "Please type a math problem or upload a text file containing one."
        stepOutput.innerHTML = ""
        return
    }

    try {
        const { result, steps } = createProblemSteps(problem)
        output.style.display = "block"
        summary.innerHTML = `<div class="solution-summary"><strong>${t("problem")}:</strong> ${problem}<br><strong>${t("answer")}:</strong> ${result !== null ? formatResult(result) : "—"}</div>`
        displaySteps(steps)
        startStepAnimation()
    } catch (error) {
        output.style.display = "block"
        summary.textContent = `Error: ${error.message}`
        stepOutput.innerHTML = ""
        stopStepAnimation()
        updatePlayStepsButtonState()
    }
}

const math = {
    pi: Math.PI,
    e: Math.E,
    i: complex(0, 1),
    complex,
    re: value => isComplex(value) ? value.re : Number(value),
    im: value => isComplex(value) ? value.im : 0,
    conj: value => isComplex(value) ? complex(value.re, -value.im) : complex(Number(value), 0),
    arg: value => isComplex(value) ? Math.atan2(value.im, value.re) : Math.atan2(0, Number(value)),
    abs: value => isComplex(value) ? Math.hypot(value.re, value.im) : Math.abs(Number(value)),
    add: (a, b) => (isComplex(a) || isComplex(b)) ? complexAdd(a, b) : Number(a) + Number(b),
    sub: (a, b) => (isComplex(a) || isComplex(b)) ? complexSub(a, b) : Number(a) - Number(b),
    mul: (a, b) => (isComplex(a) || isComplex(b)) ? complexMul(a, b) : Number(a) * Number(b),
    div: (a, b) => (isComplex(a) || isComplex(b)) ? complexDiv(a, b) : Number(a) / Number(b),
    sin: value => isComplex(value) ? complexSin(value) : Math.sin(Number(value)),
    cos: value => isComplex(value) ? complexCos(value) : Math.cos(Number(value)),
    tan: value => isComplex(value) ? complexTan(value) : Math.tan(Number(value)),
    asin: value => Math.asin(Number(value)),
    acos: value => Math.acos(Number(value)),
    atan: value => Math.atan(Number(value)),
    exp: value => isComplex(value) ? complexExp(value) : Math.exp(Number(value)),
    log: value => isComplex(value) ? complexLog(value) : Math.log10(Number(value)),
    ln: value => isComplex(value) ? complexLog(value) : Math.log(Number(value)),
    sqrt: value => isComplex(value) ? complexSqrt(value) : Math.sqrt(Number(value)),
    floor: value => Math.floor(Number(value)),
    ceil: value => Math.ceil(Number(value)),
    round: value => Math.round(Number(value)),
    max: (...values) => Math.max(...values.map(Number)),
    min: (...values) => Math.min(...values.map(Number)),
    gcd: (a, b) => {
        a = Math.abs(Math.trunc(a));
        b = Math.abs(Math.trunc(b));
        while (b) [a, b] = [b, a % b]
        return a
    },
    lcm: (a, b) => {
        if (a === 0 || b === 0) return 0
        return Math.abs(Math.trunc(a * b) / math.gcd(a, b))
    },
    mod: (a, b) => Number(a) - Math.trunc(Number(a) / Number(b)) * Number(b),
    matrix: matrix => {
        if (!Array.isArray(matrix)) throw new Error("Matrix must be defined as an array.")
        return matrix
    },
    transpose: matrixTranspose,
    det: matrixDet,
    inv: matrixInverse,
    trace: matrixTrace,
    rank: matrixRank,
    limit: (expr, variable, point, direction = "both") => {
        if (typeof expr !== "string") throw new Error("Limit requires an expression string.")
        const delta = 1e-6
        const target = Number(point)
        const f = x => evaluateExpression(expr, x)
        if (direction === "left") return f(target - delta)
        if (direction === "right") return f(target + delta)
        return (f(target - delta) + f(target + delta)) / 2
    },
    derivative: (expr, variable, point) => {
        if (typeof expr !== "string") throw new Error("Derivative requires an expression string.")
        const target = Number(point)
        const h = 1e-5
        const f = x => evaluateExpression(expr, x)
        return (f(target + h) - f(target - h)) / (2 * h)
    },
    solve: (expr, variableName) => {
        if (typeof expr !== "string") throw new Error("Solve requires an equation string.")
        if (typeof variableName !== "string") throw new Error("Solve requires a variable name.")
        const parts = expr.split("=")
        if (parts.length !== 2) throw new Error("Solve supports a single equation with one '=' sign.")
        const left = parts[0]
        const right = parts[1]
        const f = x => evaluateExpression(`${left} - (${right})`, x)
        let a = -1000
        let b = 1000
        let fa = f(a)
        let fb = f(b)
        if (Math.abs(fa) < 1e-9) return a
        if (Math.abs(fb) < 1e-9) return b
        if (Math.sign(fa) === Math.sign(fb)) throw new Error("Unable to find a root in the default range.")
        for (let i = 0; i < 60; i++) {
            const mid = (a + b) / 2
            const fm = f(mid)
            if (Math.abs(fm) < 1e-9) return mid
            if (Math.sign(fa) !== Math.sign(fm)) {
                b = mid
                fb = fm
            } else {
                a = mid
                fa = fm
            }
        }
        return (a + b) / 2
    }
}

function complexSqrt(value) {
    const z = complexify(value)
    const r = Math.hypot(z.re, z.im)
    const real = Math.sqrt((r + z.re) / 2)
    const imag = Math.sign(z.im) * Math.sqrt((r - z.re) / 2)
    return complex(real, imag)
}

function sanitizeExpression(expression) {
    if (typeof expression !== "string") throw new Error("Expression must be text.")
    let expr = expression.trim()
    expr = expr.replace(/÷/g, "/").replace(/×/g, "*").replace(/\^/g, "**")
    expr = expr.replace(/(\d)\s*x\b/g, "$1*x")
    expr = expr.replace(/(\d)\s*\(/g, "$1*(")
    expr = expr.replace(/\)\s*\(/g, ")*(")
    expr = expr.replace(/(\d)\s*i\b/g, "$1*i")
    const unsafe = /(?:constructor|prototype|window|globalThis|Function|eval|process|require|module|document|self|import|export|this|new)\b/i
    if (unsafe.test(expr)) throw new Error("Invalid expression content.")
    const stripped = expr.replace(/(['\"])(?:\\.|[^\\])*?\1/g, '""')
    const tokens = stripped.match(/[A-Za-z_]\w*/g) || []
    for (const token of tokens) {
        if (!allowedNames.has(token)) {
            throw new Error(`Invalid function or variable: ${token}`)
        }
    }
    return expr
}

function evaluateExpression(expression, xValue) {
    const sanitized = sanitizeExpression(expression)
    const names = Array.from(allowedNames).filter(name => name !== "x")
    const func = Function(
        "math",
        "x",
        `"use strict"; const { ${names.join(", ")} } = math; return (${sanitized});`
    )
    return func(math, xValue)
}

function solveEquation(problem) {
    const parts = problem.split("=")
    if (parts.length !== 2) {
        throw new Error("Please enter a single equation with one '=' sign.")
    }
    const left = parts[0].trim()
    const right = parts[1].trim()
    const f = x => evaluateExpression(`${left} - (${right})`, x)

    const steps = []
    steps.push(`Rewrite the equation as: (${left}) - (${right}) = 0`)

    let a = -1000
    let b = 1000
    let fa = f(a)
    let fb = f(b)
    steps.push(`Evaluate the function at the edges: f(${a}) = ${formatResult(fa)}, f(${b}) = ${formatResult(fb)}`)

    if (Math.abs(fa) < 1e-9) return { value: a, steps: [...steps, `Found root at x = ${formatResult(a)}.`] }
    if (Math.abs(fb) < 1e-9) return { value: b, steps: [...steps, `Found root at x = ${formatResult(b)}.`] }
    if (Math.sign(fa) === Math.sign(fb)) {
        throw new Error("Unable to find a root in the default range. Try a simpler expression or add solve(\"...,x\").")
    }

    for (let i = 0; i < 80; i++) {
        const mid = (a + b) / 2
        const fm = f(mid)
        steps.push(`Iteration ${i + 1}: check x = ${formatResult(mid)}, f(x) = ${formatResult(fm)}`)
        if (Math.abs(fm) < 1e-9) {
            return { value: mid, steps: [...steps, `Root found at x = ${formatResult(mid)}.`] }
        }
        if (Math.sign(fa) !== Math.sign(fm)) {
            b = mid
            fb = fm
        } else {
            a = mid
            fa = fm
        }
    }

    const result = (a + b) / 2
    return { value: result, steps: [...steps, `Final approximate root: x = ${formatResult(result)}.`] }
}

input.addEventListener("change", () => {
    const file = input.files[0]
    if (!file) return

    const reader = new FileReader()
    reader.onload = (event) => {
        const fileText = event.target.result.trim()
        questionInput.value = fileText
        innerUploadImage.querySelector("span").style.display = "none"
        innerUploadImage.querySelector("p").style.display = "none"
        innerUploadImage.querySelector("#icon").style.display = "none"
    }
    reader.readAsText(file)
})

solveButton.addEventListener("click", generateResponse)
if (playStepsButton) {
    playStepsButton.addEventListener("click", togglePlaySteps)
}
innerUploadImage.addEventListener("click", () => {
    input.click()
})

let currentStepIndex = 0
let stepInterval = null

function stopStepAnimation() {
    if (stepInterval) {
        clearInterval(stepInterval)
        stepInterval = null
    }
}

function startStepAnimation() {
    if (stepOutput.children.length === 0) return
    stopStepAnimation()
    currentStepIndex = 0
    highlightStep(currentStepIndex)
    stepInterval = setInterval(() => {
        currentStepIndex = (currentStepIndex + 1) % stepOutput.children.length
        highlightStep(currentStepIndex)
    }, 2500)
}
