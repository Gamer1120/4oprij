package clientserver;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;

/**
 * P2 prac wk4. <br>
 * Client.
 * 
 * @author Theo Ruys
 * @version 2005.02.21
 */
public class Client extends Thread {

	private String clientName;
	private MessageUI mui;
	private Socket sock;
	private BufferedReader in;
	private BufferedWriter out;
	private boolean loop;

	/**
	 * Constructs a Client-object and tries to make a socket connection
	 */
	public Client(String name, InetAddress host, int port, MessageUI muiArg)
			throws IOException {
		this.clientName = name;
		this.sock = new Socket(host, port);
		this.mui = muiArg;
		this.in = new BufferedReader(new InputStreamReader(
				sock.getInputStream()));
		this.out = new BufferedWriter(new OutputStreamWriter(
				sock.getOutputStream()));
		this.loop = true;
	}

	/**
	 * Reads the messages in the socket connection. Each message will be
	 * forwarded to the MessageUI
	 */
	public void run() {
		sendMessage(getClientName());
		while (loop) {
			try {
				String message = in.readLine();
				if (message != null) {
					if ("EXIT".equals(message)) {
						shutdown();
					}
					mui.addMessage(message);
				}
			} catch (IOException ex) {
				shutdown();
			}
		}
	}

	/** send a message to a ClientHandler. */
	public void sendMessage(String msg) {
		try {
			out.write(msg);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			shutdown();
		}
	}

	/** close the socket connection. */
	public void shutdown() {
		loop = false;
		try {
			sock.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		System.exit(0);
	}

	/** returns the client name */
	public String getClientName() {
		return clientName;
	}

} // end of class Client
