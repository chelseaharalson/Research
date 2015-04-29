import java.util.*;
import java.io.*;

public class MapTask {
	public static void main(String []args) {

		if (foo()) {
			System.out.println("Hi");
			bar();
		}

	}

	public static boolean foo() {
		JobConf job = new JobConf();
		return job.getCompressMapOutput();
	}

	public static void bar() {
		System.out.println("bar()");
	}
	
}
