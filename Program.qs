namespace qperceptron {

    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Arrays;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Logical;
    open Microsoft.Quantum.Diagnostics;
    
    /// # Описание
    /// увеличение на единицу числового значения в массиве кубитов (рассматриваемых как регистр)
    /// то есть трансформация вида |k> -> |k+1>
    operation Inc(target: Qubit[]) : Unit is Ctl {
        let n = Length(target);
        for idx in 1..n {
            Controlled X(target[0..n-idx-1], target[n-idx]);
        } 
    }

    /// # Описание
    /// увеличение на указанную величину числового значения в массиве кубитов (рассматриваемых как регистр)
    /// то есть трансформация вида |k>|value> -> |k+value>|value>
    operation Add(target: Qubit[], value: Qubit[]) : Unit {
        let n = Length(target);
        use (qubits) = (Qubit[2]) {
            for idx in 0..n-1 {
                let carry = qubits[idx%2];
                let next = qubits[1-(idx%2)];
                // вычисляем следующее значение флага переноса разряда
                // next = carry+target[idx]+value[idx]>=2
                Controlled X([carry, target[idx]], next);
                Controlled X([carry, value[idx]], next);
                Controlled X([target[idx], value[idx]], next);
                Controlled X([carry, target[idx], value[idx]], next);
                // target[idx] = carry^target[idx]^value[idx]
                Controlled X([value[idx]], target[idx]);
                Controlled X([carry], target[idx]);
                Reset(carry);
            } 
            ResetAll(qubits);
        }
    }
    
    /// # Описание
    /// увеличение на указанную величину числового значения в массиве кубитов (рассматриваемых как регистр)
    /// то есть трансформация вида |k> -> |k+value>
    operation AddInt(target: Qubit[], value: Int) : Unit {
        let n = Length(target);
        mutable bools = [false, size=n];
        if(value>0) {
            let tmp = IntAsBoolArray(value, n);
            for i in 0..n-1 {
                set bools w/= i <- tmp[i];
            }
        }
        if(value<0) { 
            // value = ~(-value)+1
            let tmp = IntAsBoolArray(-value, n);
            mutable carry = true;
            for i in 0..n-1 {
                let next = carry and not tmp[i];
                set bools w/= i <- (not tmp[i] and not carry) or (tmp[i] and carry);
                set carry = next;
            } 
        }

        use (qubits) = (Qubit[2]) {
            for idx in 0..n-1 {
                let carry = qubits[idx%2];
                let next = qubits[1-(idx%2)];
                // вычисляем следующее значение флага переноса разряда
                if(bools[idx]) {
                    // next = carry*target[idx]^carry^target[idx] = carry|target[idx]
                    Controlled X([carry, target[idx]], next);
                    Controlled X([carry], next);
                    Controlled X([target[idx]], next);
                }
                else {
                    // next = carry*target[idx] = carry&target[idx]
                    Controlled X([carry, target[idx]], next);
                }
                
                // добавляем текушее значение флага переноса и добавляемого бита
                Controlled X([carry], target[idx]);
                if(bools[idx]) {
                    X(target[idx]);
                }
                Reset(carry);
            } 
            ResetAll(qubits);
        }
    }

    /// # Описание
    /// вспомогательный метод для копирования значений массива кубитов
    operation Copy(source: Qubit[], target: Qubit[]) : Unit {
        let n = Length(source);
        for i in 0..(n-1) {
            Controlled X([source[i]], target[i]);
        }
    }

    /// # Описание
    /// измерение значений (коллапсирование) кубитов в массиве (который рассматриваем как один регистр)
    operation Measure(qubits: Qubit[]) : Bool[] {
        let results = ForEach(M, qubits);
        return ResultArrayAsBoolArray(results);
    }

    /// # Описание
    /// измерение значений (коллапсирование) кубитов в массиве (который рассматриваем как один регистр)
    operation MeasureWeights(n: Int, m: Int, qubits: Qubit[]) : Int[] {
        let results = ForEach(M, qubits);
        mutable w = [0, size=n+1];
        for i in 0..n {
            let j = ResultArrayAsInt(results[i*m..(i+1)*m-1]);
            if((j&&&(2^(m-1))) == 0) {
                set w w/= i <- j;
            }
            else {
                set w w/= i <- -((j^^^(2^m-1))+1);
            }
        }
        return w;
    }

    /// # Описание
    /// подсчёт суммы весов для заданного значения аргумента
    operation SumOfWeights(n: Int, m: Int, arg: Bool[], W: Qubit[], target: Qubit[]) : Unit {
        // target = -W0 = ~W0 + 1
        Copy(W[0..m-1], target);
        ApplyToEach(X, target);
        Inc(target);

        for i in 1..n {
            if(arg[i-1]) {
                Add(target, W[i*m..(i+1)*m-1]);
            }
        }
    }

    /// # Описание
    /// подсчёт числа ошибок для заданной выборки
    operation CountErrors(n: Int, m: Int, l: Int, args: Bool[][], values: Bool[], W: Qubit[], target: Qubit[]) : Unit {
        for i in 0..l-1 {
            use (qubits) = (Qubit[m]) {
                SumOfWeights(n, m, args[i], W, qubits);
                if(not values[i]) {
                    X(qubits[m-1]);
                }
                Controlled Inc([qubits[m-1]],target);
                ResetAll(qubits);
            }
        }
    }

    /// # Описание
    /// реализация оракла, необходимого для алгоритма гровера
    /// соответственно, мы считаем, что правильное решение - это то, которое не имеет ошибок
    operation NoErrorOracle(n: Int, m: Int, l: Int, args: Bool[][], values: Bool[], W: Qubit[], target: Qubit) : Unit {
        use (error) = (Qubit[m]) {
            CountErrors(n, m, l, args, values, W, error);
            ApplyToEach(X, error);
            Controlled X(error, target);
            ResetAll(error);
        }
    }

    /// # Описание
    /// шаг для алгоритма гровера
    /// отражение от решения    
    operation ReflectAboutSolution(oracle : (Qubit[], Qubit) => Unit, register : Qubit[]) : Unit {
        use (target)=(Qubit()){
            within {
                X(target);
                H(target);
            }
            apply {
                oracle(register, target);
            }
        }
    }

    /// # Описание
    /// шаг для алгоритма гровера
    /// отражение от H|0>
    operation ReflectAboutUniform(inputQubits : Qubit[]) : Unit {
        within {
            ApplyToEachA(H, inputQubits);
            ApplyToEachA(X, inputQubits);
        }
        apply {
            Controlled Z(Most(inputQubits), Tail(inputQubits));
        }
    }

    /// # Описание
    /// алгоритм гровера
    operation RunGroversSearch(register : Qubit[], oracle : (Qubit[], Qubit) => Unit, iterations : Int) : Unit {
        ApplyToEach(H, register);
        for _ in 1 .. iterations {
            ReflectAboutSolution(oracle, register);
            ReflectAboutUniform(register);
        }
    }

    
    /// # Описание
    /// генерация параметров случайный гиперплоскости
    operation RandomWeights(n: Int, m: Int) : Int[] {
        use (qubits)=(Qubit[m*(n+1)]){
            ApplyToEach(H, qubits);
            let w = MeasureWeights(n, m, qubits);
            ResetAll(qubits);
            return w;
        }
    } 

    /// # Описание
    /// генерация случайных данных, как обучающей последовательности
    operation RandomTrain(n: Int, m: Int, w: Int[], l: Int) : (Bool[][],Bool[]) {
        mutable args = [[false, size=n], size = l];
        mutable values = [false, size = l];
        use qubits = Qubit[n] {
            for idx in 0..l-1 {
                ApplyToEach(H, qubits);
                let arg = Measure(qubits);
                mutable s = -w[0];
                for j in 1..n {
                    if(arg[j-1]) {
                        set s+=w[j];
                    }
                }
                let value = s>=0;
                set args w/= idx <- arg;
                set values w/= idx <- value;
                ResetAll(qubits);
            }
        }
        return (args,values);
    }

    @EntryPoint()
    operation Main(n: Int, m: Int, l: Int) : Unit {
        Message("Hello quantum world!");

        // подготавливаем случайные данные
        mutable rand_w = [0, size=n+1];
        mutable (args,values)=([[false, size=n],size=l],[false,size=l]);
        mutable isAllZero = false;
        mutable isAllOne = false;

        repeat {
            let temp_w = RandomWeights(n, 2);
            let (temp_args,temp_values) = RandomTrain(n, m, temp_w, l);
            set isAllOne = true;
            set isAllZero = true;
            for i in 0..n {
                set rand_w w/= i <- temp_w[i];
            } 
            for i in 0..l-1 {
                set args w/= i <- temp_args[i];
                set values w/= i <- temp_values[i];
                set isAllOne = isAllOne and values[i];
                set isAllZero = isAllZero and not values[i];
            } 
        }
        until (not isAllOne and not isAllZero);

        Message($"n={n} m={m} l={l} m*(n+1)={m*(n+1)} rand_w={rand_w}");
        
        for i in 0..l-1 {
            Message($"TrainData: {args[i]} -> {values[i]}");
        }

        let noErrorOracle = NoErrorOracle(n, m, l, args, values, _, _);

        // проверка правильности работы оракла
        use (qubits, oracle)=(Qubit[m*(n+1)],Qubit()) {
            for i in 0..n {
                AddInt(qubits[i*m..(i+1)*m-1], rand_w[i]); 
            }
            noErrorOracle(qubits, oracle);
            let w = MeasureWeights(n, m, qubits);
            Message($"SelfCheck: {w} ... oracle = {M(oracle)}");
            if(M(oracle)==One){
                Message($"SelfCheck: Success!!! {w}");
            }
            ResetAll(qubits);
            Reset(oracle);
        }

        let groverIterations = Round(PI()/4.0*Sqrt(IntAsDouble(2^(m*(n+1)))));
        Message($"GroversSearch: groverIterations = {groverIterations}?");

        mutable isSuccess = false;

        // применяем алгоритм гровера
        // точное число шагов у алгоритма мы не знаем (знаем только оценку)
        // поэтому запускаем с разными значениями итераций
        // Повторение итераций после groverIterations сопровождается снижением этой вероятности
        // вплоть до практически нулевой вероятности успеха на итерации 2*groverIterations.
        // После этого вероятность снова возрастает до итерации 3*groverIterations и т. д.
        // В практических приложениях обычно неизвестно, сколько решений имеет ваша задача, 
        // прежде чем вы решите ее. Эффективной стратегией для решения этой проблемы является 
        // "предположение" количества решений путем постепенного увеличения степени двойки (т. е. 1,2,4,8,...).
        // Одно из этих предположений будет достаточно близким для того, чтобы алгоритм нашел решение
        // со средним числом итераций около SQRT(2^n/S) 

        mutable currenIterations = 1;
        set isSuccess = false;
        repeat{
            let repeatTests = 3;
            mutable currentTest = 0;
            repeat {
                set currentTest += 1;
                use (qubits, oracle) = (Qubit[m*(n+1)], Qubit()){
                    RunGroversSearch(qubits, noErrorOracle, currenIterations);
                    noErrorOracle(qubits, oracle);
                    let w = MeasureWeights(n, m, qubits);
                    Message($"GroversSearch: iterations = {currenIterations} ... {w} ... oracle = {M(oracle)}");
                    if(M(oracle)==One){
                        set isSuccess = true;
                        Message($"GroversSearch: Success!!! {w}");
                    }
                    ResetAll(qubits);
                    Reset(oracle);
                }
            }
            until(currentTest>=repeatTests or isSuccess);
            set currenIterations *= 2;
        }
        until (isSuccess);
    }
}
