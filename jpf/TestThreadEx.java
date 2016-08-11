class TestThreadEx {
   public static MyObject1 Lock1 = new MyObject1();
   public static MyObject2 Lock2 = new MyObject2();
   public static MyObject3 Lock3 = new MyObject3();
   public static MyObject4 Lock4 = new MyObject4();
   public static MyObject5 Lock5 = new MyObject5();

   public static class MyObject1 {

   }
   public static class MyObject2 {
      
   }
   public static class MyObject3 {
      
   }
   public static class MyObject4 {
      
   }
   public static class MyObject5 {
      
   }
   
   public static void main(String args[]) {
   
      ThreadDemo1 T1 = new ThreadDemo1();
      ThreadDemo2 T2 = new ThreadDemo2();
      ThreadDemo3 T3 = new ThreadDemo3();
      ThreadDemo4 T4 = new ThreadDemo4();
      ThreadDemo5 T5 = new ThreadDemo5();
      T2.start();
      T4.start();
      T5.start();
      T1.start();
      T3.start();

      addNum(2,4);
   }
   
   private static class ThreadDemo1 extends Thread {
      public void run() {
         synchronized (Lock1) {
            System.out.println("Thread 1: Holding lock 1...");
            try { Thread.sleep(10); }
            catch (InterruptedException e) {}
            System.out.println("Thread 1: Waiting for lock 2...");
            synchronized (Lock2) {
               System.out.println("Thread 1: Holding lock 1 & 2...");
            }
         }
      }
   }

   private static class ThreadDemo2 extends Thread {
      public void run() {
         synchronized (Lock3) {
            System.out.println("Thread 2: Holding lock 3...");
            try { Thread.sleep(10); }
            catch (InterruptedException e) {}
            System.out.println("Thread 2: Waiting for lock 4...");
            synchronized (Lock4) {
               System.out.println("Thread 2: Holding lock 3 & 4...");
            }
         }
      }
   } 

   private static class ThreadDemo3 extends Thread {
      public void run() {
         synchronized (Lock2) {
            System.out.println("Thread 3: Holding lock 2...");
            try { Thread.sleep(10); }
            catch (InterruptedException e) {}
            System.out.println("Thread 3: Waiting for lock 1...");
            synchronized (Lock1) {
               System.out.println("Thread 3: Holding lock 1 & 2...");
            }
         }
      }
   } 

      private static class ThreadDemo4 extends Thread {
      public void run() {
         synchronized (Lock4) {
            System.out.println("Thread 4: Holding lock 4...");
            try { Thread.sleep(10); }
            catch (InterruptedException e) {}
            System.out.println("Thread 4: Waiting for lock 5...");
            synchronized (Lock5) {
               System.out.println("Thread 4: Holding lock 4 & 5...");
            }
         }
      }
   } 

      private static class ThreadDemo5 extends Thread {
      public void run() {
         synchronized (Lock5) {
            System.out.println("Thread 5: Holding lock 5...");
         }
      }
   } 

   public static void addNum(int x, int y) {
   	int z = x + y;
      increment(z);
   }

   public static synchronized void increment(int z) {
      z++;
   }
}