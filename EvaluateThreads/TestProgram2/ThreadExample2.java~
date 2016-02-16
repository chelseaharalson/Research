public class ThreadExample2 {

    public static void main(String[] args) {
	foo();
        (new Thread(new HelloRunnable())).start();
        (new Thread(new GoodByeRunnable())).start();
	(new Thread(new T1())).start();
    }

    public static void foo() {
	System.out.println("Hi from foo()!");
    }
    
}

class HelloRunnable implements Runnable {
    public void printHi() {
        for (int i = 0; i < 5; i++) {
            System.out.println("Hi " + i);
        }
    }
    public void run() {
        printHi();
        System.out.println("Hello from a thread!");
    }
}

class GoodByeRunnable implements Runnable {
    public int addNum() {
        int x = 1 + 2;
        return x;
    }
    public void printBye() {
        for (int i = 0; i < 2; i++) {
            System.out.println("Bye " + i);
        }
    }
    public void run() {
        int a = addNum();
        printBye();
        System.out.println("GoodBye from a thread! " + a);
    }
}

class T1 implements Runnable {
    public void bar() {
	System.out.println("Hi from bar()!");
	(new Thread(new T2())).start();
    }
    public void run() {
	bar();
        System.out.println("Hi from T1 thread!");
    }
}

class T2 implements Runnable {
    public void zot() {
	System.out.println("Hi from zot()!");
    }
    public void run() {
	zot();
        System.out.println("Hi from T2 thread!");
    }
}
