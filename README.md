Connect4 Programming Project Michael Koopman s1401335 Sven Konings s1534130 P06
======

How do I run your solution?
1. Compile all files. 
2. Execute src/server/ServerGUI.java. This starts the GUI for the server.
3. Enter the port the Server will be listening to in the Port field.
4. Click Start Listening.
5. Execute src/client/ClientTUI.java. This starts the TUI for the client.
6. Enter localhost as IP, and the port you just entered in the ServerGUI as port.
7. Enter your name. If you want to use a ComputerPlayer with a Strategy instead,
   you can also say this here (instructions are in the TUI).
8. You're now connected to the Server. If you want to play games against a ComputerPlayer,
   just start another ClientTUI with a Strategy, and INVITE him, and then ACCEPT him on the
   ComputerPlayer's TUI.
   
Where can I find the report?
It's in the doc folder, and it's called 
"Verslag Programmeerproject Connect4 Michael Koopman s1401335 en Sven Konings s1534130.pdf"

Where can I find the source files?
In the src folder. The names of the folders in the src folder are the names of the packages.

Note: The use for PossibleDiagonals.xlsx file you can find in the doc folder is described
in the Javadoc of BoardTest.java.