import java.util.*;
import java.io.*;

public class JobConf {

	Configuration conf = new Configuration();
	
	public boolean getCompressMapOutput() {
		return conf.getBoolean("mapred.compress.map.output", false);
	}

}