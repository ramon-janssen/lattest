package com.lattest.examples.template;

import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.Collections;
import java.util.List;

import com.fasterxml.jackson.core.JsonFactory;
import com.fasterxml.jackson.core.JsonFactoryBuilder;
import com.fasterxml.jackson.core.JsonParser;
import com.fasterxml.jackson.databind.ObjectMapper;

public class App {
	static class Implementation {
		private Integer state = 0;
		private boolean confirmInput = false;
	
		private void processInput(GateValue input) {
			assert input.gate.equals("water");
			assert input.values.size() == 1;
			assert input.values.get(0).type == "int";
			Integer intParam = (Integer) input.values.get(0).value;
			if (state != null) {
				state += intParam;
			}
			confirmInput = true;
		}
		
		private GateValue generateOutput() {
			if (state != null && !confirmInput && state >= 15) {
				state = null;
				return new GateValue("coffee", Collections.emptyList());
			} else if (confirmInput && state != null) {
				confirmInput = false;
				return new GateValue("ok", Collections.singletonList(new GateValueParameter("int", state)));
			}
			return null;
		}
		
		@Override
		public String toString() {
			return "(" + state + "," + confirmInput + ")";
		}
	}
	
	private static class GateValueParameter {
		@SuppressWarnings("unused")
		public GateValueParameter() {
			
		}
		
		public GateValueParameter(String type, Object value) {
			this.type = type;
			this.value = value;
		}
		public String type;
		public Object value;
		@Override
		public String toString() {
			return "{ type: " + type.toString() + ", value: " + this.value.toString() + " }";
		}
	}
	
	private static class GateValue {
		@SuppressWarnings("unused")
		public GateValue() {
			
		}
		
		public GateValue(String gate, List<GateValueParameter> values) {
			this.gate = gate;
			this.values = values;
		}

		public String gate;
		public List<GateValueParameter> values;
		
		@Override
		public String toString() {
			return GateValue.class.getSimpleName() + " { gate: " + gate.toString() + ", values: " + this.values.toString() + " }";
		}
	}
	
	public static void main(String[] args) {
		try (ServerSocket server = new ServerSocket(2929)) {
			while (true) {
				System.out.println("socket listening on port 2929");
				Socket socket = server.accept();
				System.out.println("connection accepted");
				if (!socket.isBound()) {
					throw new RuntimeException("socket failed to bind to address");
				}
				InputStream in = socket.getInputStream();
				OutputStream out = socket.getOutputStream();
				ObjectMapper mapper = new ObjectMapper();
				System.out.println("creating parser");
				 // charset detection will block parser creation until it read a few bytes of input, which blocks the entire SUT if the input is too short, or if there is no input at all before an output is given first
				JsonFactory jf = new JsonFactoryBuilder().configure(JsonFactory.Feature.CHARSET_DETECTION, false).build();
				try (JsonParser parser = jf.createParser(in)) {
					Implementation impl = new Implementation();
					Object jsonInput;
					do {
						String startingState = impl.toString();
						for (GateValue output = impl.generateOutput(); output != null; output = impl.generateOutput()) {
							ByteArrayOutputStream s = new ByteArrayOutputStream();
							mapper.writeValue(s, output);
							s.write('\n');
							System.out.println(startingState + " ---!" + output + "---> " + impl);
							out.write(s.toByteArray());
							out.flush();
							
							startingState = impl.toString();
						}
						//System.out.println("reading input");
						jsonInput = mapper.readValue(parser, GateValue.class);
						//jsonInput = mapper.readTree(parser);
						if (jsonInput != null) {
							try {
								//System.out.println("parsed input: " + jsonInput);
								impl.processInput((GateValue) jsonInput);
								System.out.println("(" + startingState + ") ---?" + jsonInput + "---> " + impl.toString());
							} catch (Exception e) {
								System.out.println("failed parsing input as int: " + jsonInput);
								throw e;
							}
						}
					} while(jsonInput != null);
				} catch (Exception e) {
					e.printStackTrace();
				}
				System.out.println("Connection closed");
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
		System.out.println("Server closed");
	}
}
