/**
 * TAPIR client binding for YCSB.
 *
 * All YCSB records are mapped to a TAPIR *key-value pair*.  For scanning
 * operations, all keys are saved (by an arbitrary hash) in a sorted set.
 */

package com.yahoo.ycsb.db;
import com.yahoo.ycsb.DB;
import com.yahoo.ycsb.DBException;
import com.yahoo.ycsb.ByteIterator;
import com.yahoo.ycsb.StringByteIterator;
import com.yahoo.ycsb.Tapir.Client;

import java.util.Vector;
import java.util.Properties;
import java.util.Map;
import java.util.Set;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

public class TapirClient extends DB {

   public class TableRow extends HashMap<String, String> {

      public TableRow(HashMap<String, String> m) {
         super(m);
      }
      
      public TableRow(String s) {
         //System.out.println(s);
         String columns[] = s.split("\n");
         for (int i = 0; i < columns.length; i++) {
            String column[] = columns[i].split("\t");
            put(column[0],column[1]);
         }
      }
      
      public String toString() {
         String ret = "";
         for (Map.Entry<String, String> column : entrySet()) {
            ret = ret + column.getKey() + "\t" + column.getValue() + "\n";
         }
         return ret;
      }
   }
            
   public static final String CONFIG = "tapir.configpath";
   public static final String NSHARDS = "tapir.nshards";
   public static final String REPLICA = "tapir.closestreplica";
   
   private Client client;
   
   public void init() throws DBException {
      Properties props = getProperties();
      String configPath = props.getProperty(CONFIG);
      int nshards = Integer.parseInt(props.getProperty(NSHARDS));
      int closestReplica = Integer.parseInt(props.getProperty(REPLICA));
      
      client = new Client(configPath, nshards, closestReplica);
   }
   
   // public void cleanup() throws DBException {
   //    IntPointer stats = client.Stats();
   // }
   
   
   /**
    * Start a database transaction. 
    */
   @Override
   public void start() throws DBException
   {
      client.Begin();
   }
   
	/**
	 * Commit the current database transaction. 
	 */
   @Override
   public void commit() throws DBException
   {
      client.Commit();
   }
   
   /**
    * Abort the current database transaction. 
    */
   @Override
   public void abort() throws DBException
   {
      client.Abort();
   }

   
   @Override
   public int read(String table, String key, Set<String> fields,
                   HashMap<String, ByteIterator> result) {
      String value = client.Get(table+key);

       //System.out.println("Read: "+ table + key + " Value:" + value);
       if (value.isEmpty()) {
          return 1;
       }

       TableRow row = new TableRow(value);

       if (fields == null) {
          result = StringByteIterator.getByteIteratorMap(row);
       } else {
          for (String field : fields) {
             if (!row.containsKey(field)) {
                return 1;
             }
             result.put(field, new StringByteIterator(row.get(field)));
          }
       }
       
       return 0;
    }

    @Override
    public int insert(String table, String key, HashMap<String, ByteIterator> values) {
       String value = client.Get(table + key);
       TableRow row = new TableRow(StringByteIterator.getStringMap(values));
       TableRow existingRow;

       //System.out.println(value);
       // This key doesn't exist, so just insert the whole row
       if (value.isEmpty()) {
          //System.out.println("Insert: "+ table + key + " Values:" + row.toString());
          return client.Put(table+key, row.toString());
       }
       // Create a row out of the existing row
       existingRow = new TableRow(value);

       // Merge in the new values
       for (Map.Entry<String, String> column : row.entrySet()) {
          existingRow.put(column.getKey(), column.getValue());
       }

       // Put the rown back in the store
       //System.out.println("Insert: "+ table + key + " Values:" + existingRow.toString());
       return client.Put(table+key, existingRow.toString());
    }

    @Override
    public int delete(String table, String key) {
       //System.out.println("Delete: " + table + key);

       String value = client.Get(table+key);

       if (value != "") {
          // Zero out the key if it exists
          return client.Put(table+key, "");
       }
       return 0;
    }

    @Override
    public int update(String table, String key, HashMap<String, ByteIterator> values) {
       //System.out.println("Update: " + table + key);

       String value = client.Get(table+key);
       TableRow row = new TableRow(StringByteIterator.getStringMap(values));
       TableRow existingRow;

       // Couldn't get the existing key, so return an error
       if (value.isEmpty()) {
          return 1;
       }

       // Create a row out of the existing row
       existingRow = new TableRow(value);

       // Update values
       for (Map.Entry<String, String> column : row.entrySet()) {
          // if the column doesn't already exist, throw an error
          if (!existingRow.containsKey(column.getKey())) {
             return 1;
          }
          // Update
          existingRow.put(column.getKey(), column.getValue());
       }

       // Put the key back in the store
       return client.Put(table+key, existingRow.toString());
    }

    @Override
    public int scan(String table, String startkey, int recordcount,
            Set<String> fields, Vector<HashMap<String, ByteIterator>> result) {
       throw new UnsupportedOperationException("Scan not supported in TAPIR.");
    }

}
