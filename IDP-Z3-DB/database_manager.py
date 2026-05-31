import os
import sqlite3
import duckdb

class DB_Manager():
    def __init__(self):
        self.database_file = "database.db"
        self.database_manager = "sqlite"
        self.queries_create_type = []
        self.queries_insert_type = []
        self.queries_create_func_and_pred = []
        self.queries_pred_enumeration = []
        self.queries_update_cart_prod = []
        self.queries_update_facts = []
        self.naive = False
        self.has_facts = False

    def close(self):
        self.conn.close()

    def clean_database(self):
        try:
            os.remove(self.database_file)
        except:
            pass

    def apply_query(self, query: str, print_query=False):
        if "INSERT" in query:
            query = query.replace('"', "'")
        if print_query:
            print(query)
        try:
            return self.cursor.execute(query)
        except Exception as e:
            print(query)
            print(e)

    def apply_query_result_is_empty(self, query: str):
        return self.apply_query(query).fetchone() is None

    def setup(self, db_lib):
        self.clean_database()
        if db_lib == "sqlite":
            self.database_manager = "sqlite"
            self.conn = sqlite3.connect(self.database_file)
        else:
            self.database_manager = "duckdb"
            self.conn = duckdb.connect()
        self.cursor = self.conn.cursor()
        self.cursor_last_result_set = self.conn.cursor()

    def init_database(self):
        for q in self.queries_create_type:
            self.apply_query(q)
            self.conn.commit()
        for q in self.queries_insert_type:
            self.apply_query(q)
            self.conn.commit()
        for q in self.queries_create_func_and_pred:
            self.apply_query(q)
        for q in self.queries_pred_enumeration:
            self.apply_query(q)
            self.conn.commit()
        for q in self.queries_update_facts:
            self.has_facts = True
            self.apply_query(q)
            self.conn.commit()
