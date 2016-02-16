package mycode_locks;

public class SynchronizedRGB {
  
  // Values must be between 0 and 255.
  private int red;
  private int green;
  private int blue;
  private String name;

  private void check(int red,
                     int green,
                     int blue) {
      if (red < 0 || red > 255
          || green < 0 || green > 255
          || blue < 0 || blue > 255) {
          throw new IllegalArgumentException();
      }
  }

  public SynchronizedRGB(int red,
                         int green,
                         int blue,
                         String name) {
      check(red, green, blue);
      this.red = red;
      this.green = green;
      this.blue = blue;
      this.name = name;
  }

  public void set(int red,
                  int green,
                  int blue,
                  String name) {
      check(red, green, blue);
      synchronized (this) {
          this.red = red;
          this.green = green;
          this.blue = blue;
          this.name = name;
      }
  }

  public synchronized int getRGB() {
      return ((red << 16) | (green << 8) | blue);
  }

  public synchronized String getName() {
      return name;
  }
  
  public synchronized void invert() {
    red = 255 - red;
    green = 255 - green;
    blue = 255 - blue;
    name = "Inverse of " + name;
  }
  
  public void startNewTask() {
    SynchronizedRGB tip = new SynchronizedRGB(this.red, this.green, this.blue, this.name);
    SyncTest t = new SyncTest();
    synchronized (tip) {
      try {
        tip.invert();
        t.getN();
      } catch (Throwable ie) {
      }
    }
  }
  
  void testType6() {
    SyncTest t6 = new SyncTest();
    String p = t6.getNa();
    synchronized (t6) {
      try {
        System.out.println("Do nothing");
      } catch (Throwable ie) {
        
      }
    }
  }

  
  public class SyncTest {
    private String n;
    public synchronized String getN() {
      return n;
    }
    
    public synchronized String getNa() {
      getType7();
      return n;
    }
    
    synchronized void getType7() {
      red = 255 - red;
    }
    
    public void type4C() {
      grayscale();
    }
    
    public void grayscale() {
      red = 255 - red;
      green = 255 - green;
      blue = 255 - blue;
      name = "Inverse of " + name;
    }
    
    SynchronizedRGB sr;
    void cleanup() {
      int taskId = sr.getRGB();
      synchronized (SynchronizedRGB.this) {
         sr.set(red, green, blue, name);
         synchronized (this) {
           try {
              sr.invert();
           } 
           catch (Throwable ie) {
           }
         }
      }
    }
  }
}