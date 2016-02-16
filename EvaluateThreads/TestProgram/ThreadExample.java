public class ThreadExample {

    public static void main(String[] args) {
        (new Thread(new HelloRunnable())).start();
        (new Thread(new GoodByeRunnable())).start();
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
